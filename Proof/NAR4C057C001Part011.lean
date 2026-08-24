import NAR4C057C001Part010

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

noncomputable def nb057_split_alpha_0011 (f : Var) (a : Var) : TAlphaWff [((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)), ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_094), (nb057_alpha_dummy_095 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_096)) (Class.cv (nb057_alpha_dummy_089))) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_097)) (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_096)) (syn_cnnc)) (syn_cplc (Class.cv (nb057_alpha_dummy_096)) (syn_c1c)) (Class.cv (nb057_alpha_dummy_096)))))) (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_098 f)) (Class.cv (nb057_alpha_dummy_091 f))) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_099 f)) (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_098 f)) (syn_cnnc)) (syn_cplc (Class.cv (nb057_alpha_dummy_098 f)) (syn_c1c)) (Class.cv (nb057_alpha_dummy_098 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0090) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0091 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0090) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0091 f) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_089))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_091 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0094) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0095 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0094) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0095 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0093 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_104), (nb057_alpha_dummy_107 f)), ((nb057_alpha_dummy_103), (nb057_alpha_dummy_106 f)), ((nb057_alpha_dummy_102), (nb057_alpha_dummy_105 f)), ((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)), ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)), ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_094), (nb057_alpha_dummy_095 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_c1c) (nb057_wpp_refl_0014 f a))) (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0010 f a)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0093 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)), ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)), ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_094), (nb057_alpha_dummy_095 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_cnnc) (nb057_wpp_refl_0016 f a))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0093 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0093 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)), ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)), ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_094), (nb057_alpha_dummy_095 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_cnnc) (nb057_wpp_refl_0016 f a))))))))))))

theorem nb057_compact_fv_empty_0090 : (nb057_alpha_dummy_122) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0288 : (nb057_alpha_dummy_122) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_122, fv_syn_c1c] using (nb057_compact_fv_empty_0090)

theorem nb057_compact_fv_empty_0091 (f : Var) : (nb057_alpha_dummy_123 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0289 (f : Var) : (nb057_alpha_dummy_123 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_123, fv_syn_c1c] using (nb057_compact_fv_empty_0091 f)

theorem nb057_compact_fv_empty_0092 : (nb057_alpha_dummy_120) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0290 : (nb057_alpha_dummy_120) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_120, fv_syn_c1c] using (nb057_compact_fv_empty_0092)

theorem nb057_compact_fv_empty_0093 (f : Var) : (nb057_alpha_dummy_121 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0291 (f : Var) : (nb057_alpha_dummy_121 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_121, fv_syn_c1c] using (nb057_compact_fv_empty_0093 f)

theorem nb057_compact_fv_empty_0094 : (nb057_alpha_dummy_118) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0292 : (nb057_alpha_dummy_118) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_118, fv_syn_c1c] using (nb057_compact_fv_empty_0094)

theorem nb057_compact_fv_empty_0095 (f : Var) : (nb057_alpha_dummy_119 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0293 (f : Var) : (nb057_alpha_dummy_119 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_119, fv_syn_c1c] using (nb057_compact_fv_empty_0095 f)

theorem nb057_compact_envfresh_0017 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_104), (nb057_alpha_dummy_107 f)), ((nb057_alpha_dummy_103), (nb057_alpha_dummy_106 f)), ((nb057_alpha_dummy_102), (nb057_alpha_dummy_105 f)), ((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)), ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)), ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)), ((nb057_alpha_dummy_122), (nb057_alpha_dummy_123 f)), ((nb057_alpha_dummy_120), (nb057_alpha_dummy_121 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_104) (nb057_alpha_dummy_107 f) (nb057_wpp_notmem_0228) (nb057_wpp_notmem_0229 f) (TEnvFresh.consFresh (nb057_alpha_dummy_103) (nb057_alpha_dummy_106 f) (nb057_wpp_notmem_0230) (nb057_wpp_notmem_0231 f) (TEnvFresh.consFresh (nb057_alpha_dummy_102) (nb057_alpha_dummy_105 f) (nb057_wpp_notmem_0232) (nb057_wpp_notmem_0233 f) (TEnvFresh.consFresh (nb057_alpha_dummy_100) (nb057_alpha_dummy_101 f) (nb057_wpp_notmem_0234) (nb057_wpp_notmem_0235 f) (TEnvFresh.consFresh (nb057_alpha_dummy_096) (nb057_alpha_dummy_098 f) (nb057_wpp_notmem_0236) (nb057_wpp_notmem_0237 f) (TEnvFresh.consFresh (nb057_alpha_dummy_097) (nb057_alpha_dummy_099 f) (nb057_wpp_notmem_0238) (nb057_wpp_notmem_0239 f) (TEnvFresh.consFresh (nb057_alpha_dummy_122) (nb057_alpha_dummy_123 f) (nb057_wpp_notmem_0288) (nb057_wpp_notmem_0289 f) (TEnvFresh.consFresh (nb057_alpha_dummy_120) (nb057_alpha_dummy_121 f) (nb057_wpp_notmem_0290) (nb057_wpp_notmem_0291 f) (TEnvFresh.consFresh (nb057_alpha_dummy_089) (nb057_alpha_dummy_091 f) (nb057_wpp_notmem_0240) (nb057_wpp_notmem_0241 f) (TEnvFresh.consFresh (nb057_alpha_dummy_088) (nb057_alpha_dummy_090 f) (nb057_wpp_notmem_0242) (nb057_wpp_notmem_0243 f) (TEnvFresh.consFresh (nb057_alpha_dummy_118) (nb057_alpha_dummy_119 f) (nb057_wpp_notmem_0292) (nb057_wpp_notmem_0293 f) (TEnvFresh.consFresh (nb057_alpha_dummy_092) (nb057_alpha_dummy_093 f) (nb057_wpp_notmem_0246) (nb057_wpp_notmem_0247 f) (TEnvFresh.consFresh (nb057_alpha_dummy_046) (nb057_alpha_dummy_049 f) (nb057_wpp_notmem_0248) (nb057_wpp_notmem_0249 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0126) (nb057_wpp_notmem_0127 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0128) (nb057_wpp_notmem_0129 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0130) (nb057_wpp_notmem_0131 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0132) (nb057_wpp_notmem_0133 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0134) (nb057_wpp_notmem_0135 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0020) (nb057_wpp_notmem_0021 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0022) (nb057_wpp_notmem_0023 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0024) (nb057_wpp_notmem_0025 f a) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))))

noncomputable def nb057_wpp_refl_0017 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_104), (nb057_alpha_dummy_107 f)), ((nb057_alpha_dummy_103), (nb057_alpha_dummy_106 f)), ((nb057_alpha_dummy_102), (nb057_alpha_dummy_105 f)), ((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)), ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)), ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)), ((nb057_alpha_dummy_122), (nb057_alpha_dummy_123 f)), ((nb057_alpha_dummy_120), (nb057_alpha_dummy_121 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0017 f a)

theorem nb057_wpp_notmem_0294 : (nb057_alpha_dummy_122) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_122, fv_syn_c0] using (nb057_compact_fv_empty_0090)

theorem nb057_wpp_notmem_0295 (f : Var) : (nb057_alpha_dummy_123 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_123, fv_syn_c0] using (nb057_compact_fv_empty_0091 f)

theorem nb057_wpp_notmem_0296 : (nb057_alpha_dummy_120) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_120, fv_syn_c0] using (nb057_compact_fv_empty_0092)

theorem nb057_wpp_notmem_0297 (f : Var) : (nb057_alpha_dummy_121 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_121, fv_syn_c0] using (nb057_compact_fv_empty_0093 f)

theorem nb057_wpp_notmem_0298 : (nb057_alpha_dummy_118) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_118, fv_syn_c0] using (nb057_compact_fv_empty_0094)

theorem nb057_wpp_notmem_0299 (f : Var) : (nb057_alpha_dummy_119 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_119, fv_syn_c0] using (nb057_compact_fv_empty_0095 f)

theorem nb057_compact_envfresh_0018 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_104), (nb057_alpha_dummy_107 f)), ((nb057_alpha_dummy_103), (nb057_alpha_dummy_106 f)), ((nb057_alpha_dummy_102), (nb057_alpha_dummy_105 f)), ((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)), ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)), ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)), ((nb057_alpha_dummy_122), (nb057_alpha_dummy_123 f)), ((nb057_alpha_dummy_120), (nb057_alpha_dummy_121 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_104) (nb057_alpha_dummy_107 f) (nb057_wpp_notmem_0250) (nb057_wpp_notmem_0251 f) (TEnvFresh.consFresh (nb057_alpha_dummy_103) (nb057_alpha_dummy_106 f) (nb057_wpp_notmem_0252) (nb057_wpp_notmem_0253 f) (TEnvFresh.consFresh (nb057_alpha_dummy_102) (nb057_alpha_dummy_105 f) (nb057_wpp_notmem_0254) (nb057_wpp_notmem_0255 f) (TEnvFresh.consFresh (nb057_alpha_dummy_100) (nb057_alpha_dummy_101 f) (nb057_wpp_notmem_0256) (nb057_wpp_notmem_0257 f) (TEnvFresh.consFresh (nb057_alpha_dummy_096) (nb057_alpha_dummy_098 f) (nb057_wpp_notmem_0258) (nb057_wpp_notmem_0259 f) (TEnvFresh.consFresh (nb057_alpha_dummy_097) (nb057_alpha_dummy_099 f) (nb057_wpp_notmem_0260) (nb057_wpp_notmem_0261 f) (TEnvFresh.consFresh (nb057_alpha_dummy_122) (nb057_alpha_dummy_123 f) (nb057_wpp_notmem_0294) (nb057_wpp_notmem_0295 f) (TEnvFresh.consFresh (nb057_alpha_dummy_120) (nb057_alpha_dummy_121 f) (nb057_wpp_notmem_0296) (nb057_wpp_notmem_0297 f) (TEnvFresh.consFresh (nb057_alpha_dummy_089) (nb057_alpha_dummy_091 f) (nb057_wpp_notmem_0262) (nb057_wpp_notmem_0263 f) (TEnvFresh.consFresh (nb057_alpha_dummy_088) (nb057_alpha_dummy_090 f) (nb057_wpp_notmem_0264) (nb057_wpp_notmem_0265 f) (TEnvFresh.consFresh (nb057_alpha_dummy_118) (nb057_alpha_dummy_119 f) (nb057_wpp_notmem_0298) (nb057_wpp_notmem_0299 f) (TEnvFresh.consFresh (nb057_alpha_dummy_092) (nb057_alpha_dummy_093 f) (nb057_wpp_notmem_0268) (nb057_wpp_notmem_0269 f) (TEnvFresh.consFresh (nb057_alpha_dummy_046) (nb057_alpha_dummy_049 f) (nb057_wpp_notmem_0270) (nb057_wpp_notmem_0271 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0156) (nb057_wpp_notmem_0157 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0158) (nb057_wpp_notmem_0159 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0160) (nb057_wpp_notmem_0161 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0162) (nb057_wpp_notmem_0163 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0164) (nb057_wpp_notmem_0165 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0046) (nb057_wpp_notmem_0047 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0048) (nb057_wpp_notmem_0049 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0050) (nb057_wpp_notmem_0051 f a) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))))

noncomputable def nb057_wpp_refl_0018 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_104), (nb057_alpha_dummy_107 f)), ((nb057_alpha_dummy_103), (nb057_alpha_dummy_106 f)), ((nb057_alpha_dummy_102), (nb057_alpha_dummy_105 f)), ((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)), ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)), ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)), ((nb057_alpha_dummy_122), (nb057_alpha_dummy_123 f)), ((nb057_alpha_dummy_120), (nb057_alpha_dummy_121 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0018 f a)

noncomputable def nb057_split_alpha_0012 (f : Var) (a : Var) : TAlphaWff [((nb057_alpha_dummy_104), (nb057_alpha_dummy_107 f)), ((nb057_alpha_dummy_103), (nb057_alpha_dummy_106 f)), ((nb057_alpha_dummy_102), (nb057_alpha_dummy_105 f)), ((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)), ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)), ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)), ((nb057_alpha_dummy_122), (nb057_alpha_dummy_123 f)), ((nb057_alpha_dummy_120), (nb057_alpha_dummy_121 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_103)) (Class.cv (nb057_alpha_dummy_104))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_102)) (syn_cun (Class.cv (nb057_alpha_dummy_103)) (Class.cv (nb057_alpha_dummy_104)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_106 f)) (Class.cv (nb057_alpha_dummy_107 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_105 f)) (syn_cun (Class.cv (nb057_alpha_dummy_106 f)) (Class.cv (nb057_alpha_dummy_107 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0098) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0099 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0097 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0102) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0103 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0101 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0098) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0099 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0097 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0102) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0103 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0101 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_104), (nb057_alpha_dummy_107 f)), ((nb057_alpha_dummy_103), (nb057_alpha_dummy_106 f)), ((nb057_alpha_dummy_102), (nb057_alpha_dummy_105 f)), ((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)), ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)), ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)), ((nb057_alpha_dummy_122), (nb057_alpha_dummy_123 f)), ((nb057_alpha_dummy_120), (nb057_alpha_dummy_121 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_c0) (nb057_wpp_refl_0018 f a))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0107 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0105 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0107 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0105 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0110) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0111 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0109 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0110) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0111 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0109 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb057_wpp_notmem_0300 : (nb057_alpha_dummy_122) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_122, fv_syn_cnnc] using (nb057_compact_fv_empty_0090)

theorem nb057_wpp_notmem_0301 (f : Var) : (nb057_alpha_dummy_123 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_123, fv_syn_cnnc] using (nb057_compact_fv_empty_0091 f)

theorem nb057_wpp_notmem_0302 : (nb057_alpha_dummy_120) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_120, fv_syn_cnnc] using (nb057_compact_fv_empty_0092)

theorem nb057_wpp_notmem_0303 (f : Var) : (nb057_alpha_dummy_121 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_121, fv_syn_cnnc] using (nb057_compact_fv_empty_0093 f)

theorem nb057_wpp_notmem_0304 : (nb057_alpha_dummy_118) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_118, fv_syn_cnnc] using (nb057_compact_fv_empty_0094)

theorem nb057_wpp_notmem_0305 (f : Var) : (nb057_alpha_dummy_119 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_119, fv_syn_cnnc] using (nb057_compact_fv_empty_0095 f)

theorem nb057_compact_envfresh_0019 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)), ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)), ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)), ((nb057_alpha_dummy_122), (nb057_alpha_dummy_123 f)), ((nb057_alpha_dummy_120), (nb057_alpha_dummy_121 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_100) (nb057_alpha_dummy_101 f) (nb057_wpp_notmem_0272) (nb057_wpp_notmem_0273 f) (TEnvFresh.consFresh (nb057_alpha_dummy_096) (nb057_alpha_dummy_098 f) (nb057_wpp_notmem_0274) (nb057_wpp_notmem_0275 f) (TEnvFresh.consFresh (nb057_alpha_dummy_097) (nb057_alpha_dummy_099 f) (nb057_wpp_notmem_0276) (nb057_wpp_notmem_0277 f) (TEnvFresh.consFresh (nb057_alpha_dummy_122) (nb057_alpha_dummy_123 f) (nb057_wpp_notmem_0300) (nb057_wpp_notmem_0301 f) (TEnvFresh.consFresh (nb057_alpha_dummy_120) (nb057_alpha_dummy_121 f) (nb057_wpp_notmem_0302) (nb057_wpp_notmem_0303 f) (TEnvFresh.consFresh (nb057_alpha_dummy_089) (nb057_alpha_dummy_091 f) (nb057_wpp_notmem_0278) (nb057_wpp_notmem_0279 f) (TEnvFresh.consFresh (nb057_alpha_dummy_088) (nb057_alpha_dummy_090 f) (nb057_wpp_notmem_0280) (nb057_wpp_notmem_0281 f) (TEnvFresh.consFresh (nb057_alpha_dummy_118) (nb057_alpha_dummy_119 f) (nb057_wpp_notmem_0304) (nb057_wpp_notmem_0305 f) (TEnvFresh.consFresh (nb057_alpha_dummy_092) (nb057_alpha_dummy_093 f) (nb057_wpp_notmem_0284) (nb057_wpp_notmem_0285 f) (TEnvFresh.consFresh (nb057_alpha_dummy_046) (nb057_alpha_dummy_049 f) (nb057_wpp_notmem_0286) (nb057_wpp_notmem_0287 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0180) (nb057_wpp_notmem_0181 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0182) (nb057_wpp_notmem_0183 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0184) (nb057_wpp_notmem_0185 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0186) (nb057_wpp_notmem_0187 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0188) (nb057_wpp_notmem_0189 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0066) (nb057_wpp_notmem_0067 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0068) (nb057_wpp_notmem_0069 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0070) (nb057_wpp_notmem_0071 f a) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))))

noncomputable def nb057_wpp_refl_0019 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)), ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)), ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)), ((nb057_alpha_dummy_122), (nb057_alpha_dummy_123 f)), ((nb057_alpha_dummy_120), (nb057_alpha_dummy_121 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0019 f a)

noncomputable def nb057_split_alpha_0013 (f : Var) (a : Var) : TAlphaWff [((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)), ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)), ((nb057_alpha_dummy_122), (nb057_alpha_dummy_123 f)), ((nb057_alpha_dummy_120), (nb057_alpha_dummy_121 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_096)) (Class.cv (nb057_alpha_dummy_089))) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_097)) (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_096)) (syn_cnnc)) (syn_cplc (Class.cv (nb057_alpha_dummy_096)) (syn_c1c)) (Class.cv (nb057_alpha_dummy_096)))))) (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_098 f)) (Class.cv (nb057_alpha_dummy_091 f))) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_099 f)) (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_098 f)) (syn_cnnc)) (syn_cplc (Class.cv (nb057_alpha_dummy_098 f)) (syn_c1c)) (Class.cv (nb057_alpha_dummy_098 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0090) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0091 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0090) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0091 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0120) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0121 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0118) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0119 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_089))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_091 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0094) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0095 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0094) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0095 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0093 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_104), (nb057_alpha_dummy_107 f)), ((nb057_alpha_dummy_103), (nb057_alpha_dummy_106 f)), ((nb057_alpha_dummy_102), (nb057_alpha_dummy_105 f)), ((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)), ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)), ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)), ((nb057_alpha_dummy_122), (nb057_alpha_dummy_123 f)), ((nb057_alpha_dummy_120), (nb057_alpha_dummy_121 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_c1c) (nb057_wpp_refl_0017 f a))) (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0012 f a)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0093 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)), ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)), ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)), ((nb057_alpha_dummy_122), (nb057_alpha_dummy_123 f)), ((nb057_alpha_dummy_120), (nb057_alpha_dummy_121 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_cnnc) (nb057_wpp_refl_0019 f a))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0093 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0093 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)), ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)), ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)), ((nb057_alpha_dummy_122), (nb057_alpha_dummy_123 f)), ((nb057_alpha_dummy_120), (nb057_alpha_dummy_121 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_cnnc) (nb057_wpp_refl_0019 f a))))))))))))

theorem nb057_wpp_notmem_0306 : (nb057_alpha_dummy_120) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_120, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0092)

theorem nb057_wpp_notmem_0307 (f : Var) : (nb057_alpha_dummy_121 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_121, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0093 f)

theorem nb057_wpp_notmem_0308 : (nb057_alpha_dummy_089) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_089, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0080)

theorem nb057_wpp_notmem_0309 (f : Var) : (nb057_alpha_dummy_091 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_091, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0081 f)

theorem nb057_wpp_notmem_0310 : (nb057_alpha_dummy_088) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_088, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0082)

theorem nb057_wpp_notmem_0311 (f : Var) : (nb057_alpha_dummy_090 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_090, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0083 f)

theorem nb057_wpp_notmem_0312 : (nb057_alpha_dummy_118) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_118, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0094)

theorem nb057_wpp_notmem_0313 (f : Var) : (nb057_alpha_dummy_119 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_119, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0095 f)

theorem nb057_wpp_notmem_0314 : (nb057_alpha_dummy_092) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_092, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0086)

theorem nb057_wpp_notmem_0315 (f : Var) : (nb057_alpha_dummy_093 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_093, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0087 f)

theorem nb057_wpp_notmem_0316 : (nb057_alpha_dummy_046) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_046, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0088)

theorem nb057_wpp_notmem_0317 (f : Var) : (nb057_alpha_dummy_049 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_049, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0089 f)

theorem nb057_compact_envfresh_0020 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_120), (nb057_alpha_dummy_121 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_120) (nb057_alpha_dummy_121 f) (nb057_wpp_notmem_0306) (nb057_wpp_notmem_0307 f) (TEnvFresh.consFresh (nb057_alpha_dummy_089) (nb057_alpha_dummy_091 f) (nb057_wpp_notmem_0308) (nb057_wpp_notmem_0309 f) (TEnvFresh.consFresh (nb057_alpha_dummy_088) (nb057_alpha_dummy_090 f) (nb057_wpp_notmem_0310) (nb057_wpp_notmem_0311 f) (TEnvFresh.consFresh (nb057_alpha_dummy_118) (nb057_alpha_dummy_119 f) (nb057_wpp_notmem_0312) (nb057_wpp_notmem_0313 f) (TEnvFresh.consFresh (nb057_alpha_dummy_092) (nb057_alpha_dummy_093 f) (nb057_wpp_notmem_0314) (nb057_wpp_notmem_0315 f) (TEnvFresh.consFresh (nb057_alpha_dummy_046) (nb057_alpha_dummy_049 f) (nb057_wpp_notmem_0316) (nb057_wpp_notmem_0317 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0218) (nb057_wpp_notmem_0219 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0220) (nb057_wpp_notmem_0221 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0222) (nb057_wpp_notmem_0223 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0224) (nb057_wpp_notmem_0225 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0226) (nb057_wpp_notmem_0227 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0100) (nb057_wpp_notmem_0101 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0102) (nb057_wpp_notmem_0103 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0104) (nb057_wpp_notmem_0105 f a) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))))))

noncomputable def nb057_wpp_refl_0020 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_120), (nb057_alpha_dummy_121 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0020 f a)

noncomputable def nb057_split_alpha_0014 (f : Var) (a : Var) : TAlphaWff [((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_118)) (Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb057_alpha_dummy_118)) (Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089))) (syn_csn (syn_c0c))))))))) (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_119 f)) (Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb057_alpha_dummy_119 f)) (Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))) (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0112) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0114 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0112) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0114 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0116) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0117 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0113) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0115 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_046))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_049 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0013 f a))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0013 f a))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_120), (nb057_alpha_dummy_121 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_ccompl (syn_csn (syn_c0c))) (nb057_wpp_refl_0020 f a))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0112) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0114 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0112) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0114 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0116) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0117 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0113) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0115 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_046))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_049 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0013 f a))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0013 f a))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_120), (nb057_alpha_dummy_121 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_ccompl (syn_csn (syn_c0c))) (nb057_wpp_refl_0020 f a)))))))))))))))))))

theorem nb057_compact_fv_empty_0096 : (nb057_alpha_dummy_146) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0318 : (nb057_alpha_dummy_146) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_146, fv_syn_c1c] using (nb057_compact_fv_empty_0096)

theorem nb057_compact_fv_empty_0097 (f : Var) : (nb057_alpha_dummy_149 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0319 (f : Var) : (nb057_alpha_dummy_149 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_149, fv_syn_c1c] using (nb057_compact_fv_empty_0097 f)

theorem nb057_compact_fv_empty_0098 : (nb057_alpha_dummy_145) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0320 : (nb057_alpha_dummy_145) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_145, fv_syn_c1c] using (nb057_compact_fv_empty_0098)

theorem nb057_compact_fv_empty_0099 (f : Var) : (nb057_alpha_dummy_148 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0321 (f : Var) : (nb057_alpha_dummy_148 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_148, fv_syn_c1c] using (nb057_compact_fv_empty_0099 f)

theorem nb057_compact_fv_empty_0100 : (nb057_alpha_dummy_144) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0322 : (nb057_alpha_dummy_144) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_144, fv_syn_c1c] using (nb057_compact_fv_empty_0100)

theorem nb057_compact_fv_empty_0101 (f : Var) : (nb057_alpha_dummy_147 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0323 (f : Var) : (nb057_alpha_dummy_147 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_147, fv_syn_c1c] using (nb057_compact_fv_empty_0101 f)

theorem nb057_compact_fv_empty_0102 : (nb057_alpha_dummy_142) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0324 : (nb057_alpha_dummy_142) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_142, fv_syn_c1c] using (nb057_compact_fv_empty_0102)

theorem nb057_compact_fv_empty_0103 (f : Var) : (nb057_alpha_dummy_143 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0325 (f : Var) : (nb057_alpha_dummy_143 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_143, fv_syn_c1c] using (nb057_compact_fv_empty_0103 f)

theorem nb057_compact_fv_empty_0104 : (nb057_alpha_dummy_138) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0326 : (nb057_alpha_dummy_138) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_138, fv_syn_c1c] using (nb057_compact_fv_empty_0104)

theorem nb057_compact_fv_empty_0105 (f : Var) : (nb057_alpha_dummy_140 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0327 (f : Var) : (nb057_alpha_dummy_140 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_140, fv_syn_c1c] using (nb057_compact_fv_empty_0105 f)

theorem nb057_compact_fv_empty_0106 : (nb057_alpha_dummy_139) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0328 : (nb057_alpha_dummy_139) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_139, fv_syn_c1c] using (nb057_compact_fv_empty_0106)

theorem nb057_compact_fv_empty_0107 (f : Var) : (nb057_alpha_dummy_141 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0329 (f : Var) : (nb057_alpha_dummy_141 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_141, fv_syn_c1c] using (nb057_compact_fv_empty_0107 f)

theorem nb057_compact_fv_empty_0108 : (nb057_alpha_dummy_131) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0330 : (nb057_alpha_dummy_131) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_131, fv_syn_c1c] using (nb057_compact_fv_empty_0108)

theorem nb057_compact_fv_empty_0109 (f : Var) : (nb057_alpha_dummy_133 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0331 (f : Var) : (nb057_alpha_dummy_133 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_133, fv_syn_c1c] using (nb057_compact_fv_empty_0109 f)

theorem nb057_compact_fv_empty_0110 : (nb057_alpha_dummy_130) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0332 : (nb057_alpha_dummy_130) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_130, fv_syn_c1c] using (nb057_compact_fv_empty_0110)

theorem nb057_compact_fv_empty_0111 (f : Var) : (nb057_alpha_dummy_132 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0333 (f : Var) : (nb057_alpha_dummy_132 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_132, fv_syn_c1c] using (nb057_compact_fv_empty_0111 f)

theorem nb057_compact_fv_empty_0112 : (nb057_alpha_dummy_136) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0334 : (nb057_alpha_dummy_136) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_136, fv_syn_c1c] using (nb057_compact_fv_empty_0112)

theorem nb057_compact_fv_empty_0113 (f : Var) : (nb057_alpha_dummy_137 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0335 (f : Var) : (nb057_alpha_dummy_137 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_137, fv_syn_c1c] using (nb057_compact_fv_empty_0113 f)

theorem nb057_compact_fv_empty_0114 : (nb057_alpha_dummy_134) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0336 : (nb057_alpha_dummy_134) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_134, fv_syn_c1c] using (nb057_compact_fv_empty_0114)

theorem nb057_compact_fv_empty_0115 (f : Var) : (nb057_alpha_dummy_135 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0337 (f : Var) : (nb057_alpha_dummy_135 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_135, fv_syn_c1c] using (nb057_compact_fv_empty_0115 f)

theorem nb057_compact_fv_empty_0116 : (nb057_alpha_dummy_125) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0338 : (nb057_alpha_dummy_125) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_125, fv_syn_c1c] using (nb057_compact_fv_empty_0116)

theorem nb057_compact_fv_empty_0117 (f : Var) : (nb057_alpha_dummy_127 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0339 (f : Var) : (nb057_alpha_dummy_127 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_127, fv_syn_c1c] using (nb057_compact_fv_empty_0117 f)

theorem nb057_compact_fv_empty_0118 : (nb057_alpha_dummy_124) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0340 : (nb057_alpha_dummy_124) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_124, fv_syn_c1c] using (nb057_compact_fv_empty_0118)

theorem nb057_compact_fv_empty_0119 (f : Var) : (nb057_alpha_dummy_126 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
