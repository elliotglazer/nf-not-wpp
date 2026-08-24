import NAR4C074C001Part009

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

theorem nb074_wpp_notmem_0302 : (nb074_alpha_dummy_117) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_117, fv_syn_cnnc] using (nb074_compact_fv_empty_0092)

theorem nb074_wpp_notmem_0303 (x : Var) : (nb074_alpha_dummy_118 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_118, fv_syn_cnnc] using (nb074_compact_fv_empty_0093 x)

theorem nb074_compact_envfresh_0021 (x : Var) : TEnvFresh [((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)), ((nb074_alpha_dummy_095), (nb074_alpha_dummy_097 x)), ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)), ((nb074_alpha_dummy_121), (nb074_alpha_dummy_122 x)), ((nb074_alpha_dummy_119), (nb074_alpha_dummy_120 x)), ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)), ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)), ((nb074_alpha_dummy_117), (nb074_alpha_dummy_118 x)), ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)), ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb074_alpha_dummy_099) (nb074_alpha_dummy_100 x) (nb074_wpp_notmem_0266) (nb074_wpp_notmem_0267 x) (TEnvFresh.consFresh (nb074_alpha_dummy_095) (nb074_alpha_dummy_097 x) (nb074_wpp_notmem_0268) (nb074_wpp_notmem_0269 x) (TEnvFresh.consFresh (nb074_alpha_dummy_096) (nb074_alpha_dummy_098 x) (nb074_wpp_notmem_0270) (nb074_wpp_notmem_0271 x) (TEnvFresh.consFresh (nb074_alpha_dummy_121) (nb074_alpha_dummy_122 x) (nb074_wpp_notmem_0298) (nb074_wpp_notmem_0299 x) (TEnvFresh.consFresh (nb074_alpha_dummy_119) (nb074_alpha_dummy_120 x) (nb074_wpp_notmem_0300) (nb074_wpp_notmem_0301 x) (TEnvFresh.consFresh (nb074_alpha_dummy_088) (nb074_alpha_dummy_090 x) (nb074_wpp_notmem_0272) (nb074_wpp_notmem_0273 x) (TEnvFresh.consFresh (nb074_alpha_dummy_087) (nb074_alpha_dummy_089 x) (nb074_wpp_notmem_0274) (nb074_wpp_notmem_0275 x) (TEnvFresh.consFresh (nb074_alpha_dummy_117) (nb074_alpha_dummy_118 x) (nb074_wpp_notmem_0302) (nb074_wpp_notmem_0303 x) (TEnvFresh.consFresh (nb074_alpha_dummy_091) (nb074_alpha_dummy_092 x) (nb074_wpp_notmem_0278) (nb074_wpp_notmem_0279 x) (TEnvFresh.consFresh (nb074_alpha_dummy_082) (nb074_alpha_dummy_084 x) (nb074_wpp_notmem_0280) (nb074_wpp_notmem_0281 x) (TEnvFresh.consFresh (nb074_alpha_dummy_081) (nb074_alpha_dummy_083 x) (nb074_wpp_notmem_0282) (nb074_wpp_notmem_0283 x) (TEnvFresh.consFresh (nb074_alpha_dummy_085) (nb074_alpha_dummy_086 x) (nb074_wpp_notmem_0284) (nb074_wpp_notmem_0285 x) (TEnvFresh.consFresh (nb074_alpha_dummy_042) (nb074_alpha_dummy_044 x) (nb074_wpp_notmem_0178) (nb074_wpp_notmem_0179 x) (TEnvFresh.consFresh (nb074_alpha_dummy_041) (nb074_alpha_dummy_043 x) (nb074_wpp_notmem_0180) (nb074_wpp_notmem_0181 x) (TEnvFresh.consFresh (nb074_alpha_dummy_001) (nb074_alpha_dummy_002 x) (nb074_wpp_notmem_0066) (nb074_wpp_notmem_0067 x) (TEnvFresh.consFresh (nb074_alpha_dummy_000) x (nb074_wpp_notmem_0068) (nb074_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb074_alpha_dummy_003) (nb074_alpha_dummy_004 x) (nb074_wpp_notmem_0070) (nb074_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))

noncomputable def nb074_wpp_refl_0021 (x : Var) : TReflOn [((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)), ((nb074_alpha_dummy_095), (nb074_alpha_dummy_097 x)), ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)), ((nb074_alpha_dummy_121), (nb074_alpha_dummy_122 x)), ((nb074_alpha_dummy_119), (nb074_alpha_dummy_120 x)), ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)), ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)), ((nb074_alpha_dummy_117), (nb074_alpha_dummy_118 x)), ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)), ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb074_compact_envfresh_0021 x)

theorem nb074_wpp_notmem_0304 : (nb074_alpha_dummy_119) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_119, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0090)

theorem nb074_wpp_notmem_0305 (x : Var) : (nb074_alpha_dummy_120 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_120, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0091 x)

theorem nb074_wpp_notmem_0306 : (nb074_alpha_dummy_088) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_088, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0074)

theorem nb074_wpp_notmem_0307 (x : Var) : (nb074_alpha_dummy_090 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_090, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0075 x)

theorem nb074_wpp_notmem_0308 : (nb074_alpha_dummy_087) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_087, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0076)

theorem nb074_wpp_notmem_0309 (x : Var) : (nb074_alpha_dummy_089 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_089, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0077 x)

theorem nb074_wpp_notmem_0310 : (nb074_alpha_dummy_117) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_117, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0092)

theorem nb074_wpp_notmem_0311 (x : Var) : (nb074_alpha_dummy_118 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_118, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0093 x)

theorem nb074_wpp_notmem_0312 : (nb074_alpha_dummy_091) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_091, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0080)

theorem nb074_wpp_notmem_0313 (x : Var) : (nb074_alpha_dummy_092 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_092, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0081 x)

theorem nb074_wpp_notmem_0314 : (nb074_alpha_dummy_082) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_082, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0082)

theorem nb074_wpp_notmem_0315 (x : Var) : (nb074_alpha_dummy_084 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_084, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0083 x)

theorem nb074_wpp_notmem_0316 : (nb074_alpha_dummy_081) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_081, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0084)

theorem nb074_wpp_notmem_0317 (x : Var) : (nb074_alpha_dummy_083 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_083, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0085 x)

theorem nb074_wpp_notmem_0318 : (nb074_alpha_dummy_085) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_085, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0086)

theorem nb074_wpp_notmem_0319 (x : Var) : (nb074_alpha_dummy_086 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_086, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0087 x)

theorem nb074_compact_envfresh_0022 (x : Var) : TEnvFresh [((nb074_alpha_dummy_119), (nb074_alpha_dummy_120 x)), ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)), ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)), ((nb074_alpha_dummy_117), (nb074_alpha_dummy_118 x)), ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)), ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb074_alpha_dummy_119) (nb074_alpha_dummy_120 x) (nb074_wpp_notmem_0304) (nb074_wpp_notmem_0305 x) (TEnvFresh.consFresh (nb074_alpha_dummy_088) (nb074_alpha_dummy_090 x) (nb074_wpp_notmem_0306) (nb074_wpp_notmem_0307 x) (TEnvFresh.consFresh (nb074_alpha_dummy_087) (nb074_alpha_dummy_089 x) (nb074_wpp_notmem_0308) (nb074_wpp_notmem_0309 x) (TEnvFresh.consFresh (nb074_alpha_dummy_117) (nb074_alpha_dummy_118 x) (nb074_wpp_notmem_0310) (nb074_wpp_notmem_0311 x) (TEnvFresh.consFresh (nb074_alpha_dummy_091) (nb074_alpha_dummy_092 x) (nb074_wpp_notmem_0312) (nb074_wpp_notmem_0313 x) (TEnvFresh.consFresh (nb074_alpha_dummy_082) (nb074_alpha_dummy_084 x) (nb074_wpp_notmem_0314) (nb074_wpp_notmem_0315 x) (TEnvFresh.consFresh (nb074_alpha_dummy_081) (nb074_alpha_dummy_083 x) (nb074_wpp_notmem_0316) (nb074_wpp_notmem_0317 x) (TEnvFresh.consFresh (nb074_alpha_dummy_085) (nb074_alpha_dummy_086 x) (nb074_wpp_notmem_0318) (nb074_wpp_notmem_0319 x) (TEnvFresh.consFresh (nb074_alpha_dummy_042) (nb074_alpha_dummy_044 x) (nb074_wpp_notmem_0210) (nb074_wpp_notmem_0211 x) (TEnvFresh.consFresh (nb074_alpha_dummy_041) (nb074_alpha_dummy_043 x) (nb074_wpp_notmem_0212) (nb074_wpp_notmem_0213 x) (TEnvFresh.consFresh (nb074_alpha_dummy_001) (nb074_alpha_dummy_002 x) (nb074_wpp_notmem_0100) (nb074_wpp_notmem_0101 x) (TEnvFresh.consFresh (nb074_alpha_dummy_000) x (nb074_wpp_notmem_0102) (nb074_wpp_notmem_0103 x) (TEnvFresh.consFresh (nb074_alpha_dummy_003) (nb074_alpha_dummy_004 x) (nb074_wpp_notmem_0104) (nb074_wpp_notmem_0105 x) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))

noncomputable def nb074_wpp_refl_0022 (x : Var) : TReflOn [((nb074_alpha_dummy_119), (nb074_alpha_dummy_120 x)), ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)), ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)), ((nb074_alpha_dummy_117), (nb074_alpha_dummy_118 x)), ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)), ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb074_compact_envfresh_0022 x)

noncomputable def nb074_split_alpha_0006 (x : Var) : TAlphaWff [((nb074_alpha_dummy_119), (nb074_alpha_dummy_120 x)), ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)), ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)), ((nb074_alpha_dummy_117), (nb074_alpha_dummy_118 x)), ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)), ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (Wff.imp (Wff.classMem (Class.cv (nb074_alpha_dummy_119)) (syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_088))))) (Wff.neg (Wff.classMem (Class.cv (nb074_alpha_dummy_119)) (syn_ccompl (syn_csn (syn_c0c)))))) (Wff.imp (Wff.classMem (Class.cv (nb074_alpha_dummy_120 x)) (syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))) (Wff.neg (Wff.classMem (Class.cv (nb074_alpha_dummy_120 x)) (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0093 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0092) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0093 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0122) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0123 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0120) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0121 x) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_088))).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_090 x))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0096) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0097 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0097 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0094) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0095 x) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb074_alpha_dummy_103), (nb074_alpha_dummy_106 x)), ((nb074_alpha_dummy_102), (nb074_alpha_dummy_105 x)), ((nb074_alpha_dummy_101), (nb074_alpha_dummy_104 x)), ((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)), ((nb074_alpha_dummy_095), (nb074_alpha_dummy_097 x)), ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)), ((nb074_alpha_dummy_121), (nb074_alpha_dummy_122 x)), ((nb074_alpha_dummy_119), (nb074_alpha_dummy_120 x)), ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)), ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)), ((nb074_alpha_dummy_117), (nb074_alpha_dummy_118 x)), ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)), ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_c1c) (nb074_wpp_refl_0019 x))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0101 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0098) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0099 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0105 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0102) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0103 x) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0101 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0098) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0099 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0105 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0102) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0103 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb074_alpha_dummy_103), (nb074_alpha_dummy_106 x)), ((nb074_alpha_dummy_102), (nb074_alpha_dummy_105 x)), ((nb074_alpha_dummy_101), (nb074_alpha_dummy_104 x)), ((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)), ((nb074_alpha_dummy_095), (nb074_alpha_dummy_097 x)), ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)), ((nb074_alpha_dummy_121), (nb074_alpha_dummy_122 x)), ((nb074_alpha_dummy_119), (nb074_alpha_dummy_120 x)), ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)), ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)), ((nb074_alpha_dummy_117), (nb074_alpha_dummy_118 x)), ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)), ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_c0) (nb074_wpp_refl_0020 x))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0109 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0107 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0109 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0107 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0112) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0113 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0110) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0111 x) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0112) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0113 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0110) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0111 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0094) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0095 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)), ((nb074_alpha_dummy_095), (nb074_alpha_dummy_097 x)), ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)), ((nb074_alpha_dummy_121), (nb074_alpha_dummy_122 x)), ((nb074_alpha_dummy_119), (nb074_alpha_dummy_120 x)), ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)), ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)), ((nb074_alpha_dummy_117), (nb074_alpha_dummy_118 x)), ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)), ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_cnnc) (nb074_wpp_refl_0021 x))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0094) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0095 x) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0094) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0095 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)), ((nb074_alpha_dummy_095), (nb074_alpha_dummy_097 x)), ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)), ((nb074_alpha_dummy_121), (nb074_alpha_dummy_122 x)), ((nb074_alpha_dummy_119), (nb074_alpha_dummy_120 x)), ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)), ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)), ((nb074_alpha_dummy_117), (nb074_alpha_dummy_118 x)), ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)), ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_cnnc) (nb074_wpp_refl_0021 x)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0093 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0092) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0093 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0122) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0123 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0120) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0121 x) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_088))).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_090 x))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0096) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0097 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0097 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0094) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0095 x) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb074_alpha_dummy_103), (nb074_alpha_dummy_106 x)), ((nb074_alpha_dummy_102), (nb074_alpha_dummy_105 x)), ((nb074_alpha_dummy_101), (nb074_alpha_dummy_104 x)), ((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)), ((nb074_alpha_dummy_095), (nb074_alpha_dummy_097 x)), ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)), ((nb074_alpha_dummy_121), (nb074_alpha_dummy_122 x)), ((nb074_alpha_dummy_119), (nb074_alpha_dummy_120 x)), ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)), ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)), ((nb074_alpha_dummy_117), (nb074_alpha_dummy_118 x)), ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)), ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_c1c) (nb074_wpp_refl_0019 x))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0101 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0098) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0099 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0105 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0102) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0103 x) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0101 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0098) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0099 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0105 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0102) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0103 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb074_alpha_dummy_103), (nb074_alpha_dummy_106 x)), ((nb074_alpha_dummy_102), (nb074_alpha_dummy_105 x)), ((nb074_alpha_dummy_101), (nb074_alpha_dummy_104 x)), ((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)), ((nb074_alpha_dummy_095), (nb074_alpha_dummy_097 x)), ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)), ((nb074_alpha_dummy_121), (nb074_alpha_dummy_122 x)), ((nb074_alpha_dummy_119), (nb074_alpha_dummy_120 x)), ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)), ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)), ((nb074_alpha_dummy_117), (nb074_alpha_dummy_118 x)), ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)), ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_c0) (nb074_wpp_refl_0020 x))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0109 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0107 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0109 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0107 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0112) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0113 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0110) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0111 x) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0112) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0113 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0110) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0111 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0094) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0095 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)), ((nb074_alpha_dummy_095), (nb074_alpha_dummy_097 x)), ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)), ((nb074_alpha_dummy_121), (nb074_alpha_dummy_122 x)), ((nb074_alpha_dummy_119), (nb074_alpha_dummy_120 x)), ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)), ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)), ((nb074_alpha_dummy_117), (nb074_alpha_dummy_118 x)), ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)), ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_cnnc) (nb074_wpp_refl_0021 x))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0094) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0095 x) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0094) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0095 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)), ((nb074_alpha_dummy_095), (nb074_alpha_dummy_097 x)), ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)), ((nb074_alpha_dummy_121), (nb074_alpha_dummy_122 x)), ((nb074_alpha_dummy_119), (nb074_alpha_dummy_120 x)), ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)), ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)), ((nb074_alpha_dummy_117), (nb074_alpha_dummy_118 x)), ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)), ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_cnnc) (nb074_wpp_refl_0021 x)))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb074_alpha_dummy_119), (nb074_alpha_dummy_120 x)), ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)), ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)), ((nb074_alpha_dummy_117), (nb074_alpha_dummy_118 x)), ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)), ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_ccompl (syn_csn (syn_c0c))) (nb074_wpp_refl_0022 x)))))

theorem nb074_compact_fv_empty_0094 : (nb074_alpha_dummy_139) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0320 : (nb074_alpha_dummy_139) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_139, fv_syn_c1c] using (nb074_compact_fv_empty_0094)

theorem nb074_compact_fv_empty_0095 (x : Var) : (nb074_alpha_dummy_142 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0321 (x : Var) : (nb074_alpha_dummy_142 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_142, fv_syn_c1c] using (nb074_compact_fv_empty_0095 x)

theorem nb074_compact_fv_empty_0096 : (nb074_alpha_dummy_138) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0322 : (nb074_alpha_dummy_138) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_138, fv_syn_c1c] using (nb074_compact_fv_empty_0096)

theorem nb074_compact_fv_empty_0097 (x : Var) : (nb074_alpha_dummy_141 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0323 (x : Var) : (nb074_alpha_dummy_141 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_141, fv_syn_c1c] using (nb074_compact_fv_empty_0097 x)

theorem nb074_compact_fv_empty_0098 : (nb074_alpha_dummy_137) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0324 : (nb074_alpha_dummy_137) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_137, fv_syn_c1c] using (nb074_compact_fv_empty_0098)

theorem nb074_compact_fv_empty_0099 (x : Var) : (nb074_alpha_dummy_140 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0325 (x : Var) : (nb074_alpha_dummy_140 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_140, fv_syn_c1c] using (nb074_compact_fv_empty_0099 x)

theorem nb074_compact_fv_empty_0100 : (nb074_alpha_dummy_135) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0326 : (nb074_alpha_dummy_135) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_135, fv_syn_c1c] using (nb074_compact_fv_empty_0100)

theorem nb074_compact_fv_empty_0101 (x : Var) : (nb074_alpha_dummy_136 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0327 (x : Var) : (nb074_alpha_dummy_136 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_136, fv_syn_c1c] using (nb074_compact_fv_empty_0101 x)

theorem nb074_compact_fv_empty_0102 : (nb074_alpha_dummy_131) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0328 : (nb074_alpha_dummy_131) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_131, fv_syn_c1c] using (nb074_compact_fv_empty_0102)

theorem nb074_compact_fv_empty_0103 (x : Var) : (nb074_alpha_dummy_133 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0329 (x : Var) : (nb074_alpha_dummy_133 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_133, fv_syn_c1c] using (nb074_compact_fv_empty_0103 x)

theorem nb074_compact_fv_empty_0104 : (nb074_alpha_dummy_132) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0330 : (nb074_alpha_dummy_132) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_132, fv_syn_c1c] using (nb074_compact_fv_empty_0104)

theorem nb074_compact_fv_empty_0105 (x : Var) : (nb074_alpha_dummy_134 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0331 (x : Var) : (nb074_alpha_dummy_134 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_134, fv_syn_c1c] using (nb074_compact_fv_empty_0105 x)

theorem nb074_compact_fv_empty_0106 : (nb074_alpha_dummy_124) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0332 : (nb074_alpha_dummy_124) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_124, fv_syn_c1c] using (nb074_compact_fv_empty_0106)

theorem nb074_compact_fv_empty_0107 (x : Var) : (nb074_alpha_dummy_126 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0333 (x : Var) : (nb074_alpha_dummy_126 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_126, fv_syn_c1c] using (nb074_compact_fv_empty_0107 x)

theorem nb074_compact_fv_empty_0108 : (nb074_alpha_dummy_123) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0334 : (nb074_alpha_dummy_123) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_123, fv_syn_c1c] using (nb074_compact_fv_empty_0108)

theorem nb074_compact_fv_empty_0109 (x : Var) : (nb074_alpha_dummy_125 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0335 (x : Var) : (nb074_alpha_dummy_125 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_125, fv_syn_c1c] using (nb074_compact_fv_empty_0109 x)

theorem nb074_compact_fv_empty_0110 : (nb074_alpha_dummy_129) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0336 : (nb074_alpha_dummy_129) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_129, fv_syn_c1c] using (nb074_compact_fv_empty_0110)

theorem nb074_compact_fv_empty_0111 (x : Var) : (nb074_alpha_dummy_130 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0337 (x : Var) : (nb074_alpha_dummy_130 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_130, fv_syn_c1c] using (nb074_compact_fv_empty_0111 x)

theorem nb074_compact_fv_empty_0112 : (nb074_alpha_dummy_127) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0338 : (nb074_alpha_dummy_127) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_127, fv_syn_c1c] using (nb074_compact_fv_empty_0112)

theorem nb074_compact_fv_empty_0113 (x : Var) : (nb074_alpha_dummy_128 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0339 (x : Var) : (nb074_alpha_dummy_128 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_128, fv_syn_c1c] using (nb074_compact_fv_empty_0113 x)

theorem nb074_compact_envfresh_0023 (x : Var) : TEnvFresh [((nb074_alpha_dummy_139), (nb074_alpha_dummy_142 x)), ((nb074_alpha_dummy_138), (nb074_alpha_dummy_141 x)), ((nb074_alpha_dummy_137), (nb074_alpha_dummy_140 x)), ((nb074_alpha_dummy_135), (nb074_alpha_dummy_136 x)), ((nb074_alpha_dummy_131), (nb074_alpha_dummy_133 x)), ((nb074_alpha_dummy_132), (nb074_alpha_dummy_134 x)), ((nb074_alpha_dummy_124), (nb074_alpha_dummy_126 x)), ((nb074_alpha_dummy_123), (nb074_alpha_dummy_125 x)), ((nb074_alpha_dummy_129), (nb074_alpha_dummy_130 x)), ((nb074_alpha_dummy_127), (nb074_alpha_dummy_128 x)), ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb074_alpha_dummy_139) (nb074_alpha_dummy_142 x) (nb074_wpp_notmem_0320) (nb074_wpp_notmem_0321 x) (TEnvFresh.consFresh (nb074_alpha_dummy_138) (nb074_alpha_dummy_141 x) (nb074_wpp_notmem_0322) (nb074_wpp_notmem_0323 x) (TEnvFresh.consFresh (nb074_alpha_dummy_137) (nb074_alpha_dummy_140 x) (nb074_wpp_notmem_0324) (nb074_wpp_notmem_0325 x) (TEnvFresh.consFresh (nb074_alpha_dummy_135) (nb074_alpha_dummy_136 x) (nb074_wpp_notmem_0326) (nb074_wpp_notmem_0327 x) (TEnvFresh.consFresh (nb074_alpha_dummy_131) (nb074_alpha_dummy_133 x) (nb074_wpp_notmem_0328) (nb074_wpp_notmem_0329 x) (TEnvFresh.consFresh (nb074_alpha_dummy_132) (nb074_alpha_dummy_134 x) (nb074_wpp_notmem_0330) (nb074_wpp_notmem_0331 x) (TEnvFresh.consFresh (nb074_alpha_dummy_124) (nb074_alpha_dummy_126 x) (nb074_wpp_notmem_0332) (nb074_wpp_notmem_0333 x) (TEnvFresh.consFresh (nb074_alpha_dummy_123) (nb074_alpha_dummy_125 x) (nb074_wpp_notmem_0334) (nb074_wpp_notmem_0335 x) (TEnvFresh.consFresh (nb074_alpha_dummy_129) (nb074_alpha_dummy_130 x) (nb074_wpp_notmem_0336) (nb074_wpp_notmem_0337 x) (TEnvFresh.consFresh (nb074_alpha_dummy_127) (nb074_alpha_dummy_128 x) (nb074_wpp_notmem_0338) (nb074_wpp_notmem_0339 x) (TEnvFresh.consFresh (nb074_alpha_dummy_082) (nb074_alpha_dummy_084 x) (nb074_wpp_notmem_0234) (nb074_wpp_notmem_0235 x) (TEnvFresh.consFresh (nb074_alpha_dummy_081) (nb074_alpha_dummy_083 x) (nb074_wpp_notmem_0236) (nb074_wpp_notmem_0237 x) (TEnvFresh.consFresh (nb074_alpha_dummy_085) (nb074_alpha_dummy_086 x) (nb074_wpp_notmem_0238) (nb074_wpp_notmem_0239 x) (TEnvFresh.consFresh (nb074_alpha_dummy_042) (nb074_alpha_dummy_044 x) (nb074_wpp_notmem_0136) (nb074_wpp_notmem_0137 x) (TEnvFresh.consFresh (nb074_alpha_dummy_041) (nb074_alpha_dummy_043 x) (nb074_wpp_notmem_0138) (nb074_wpp_notmem_0139 x) (TEnvFresh.consFresh (nb074_alpha_dummy_001) (nb074_alpha_dummy_002 x) (nb074_wpp_notmem_0020) (nb074_wpp_notmem_0021 x) (TEnvFresh.consFresh (nb074_alpha_dummy_000) x (nb074_wpp_notmem_0022) (nb074_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb074_alpha_dummy_003) (nb074_alpha_dummy_004 x) (nb074_wpp_notmem_0024) (nb074_wpp_notmem_0025 x) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))

noncomputable def nb074_wpp_refl_0023 (x : Var) : TReflOn [((nb074_alpha_dummy_139), (nb074_alpha_dummy_142 x)), ((nb074_alpha_dummy_138), (nb074_alpha_dummy_141 x)), ((nb074_alpha_dummy_137), (nb074_alpha_dummy_140 x)), ((nb074_alpha_dummy_135), (nb074_alpha_dummy_136 x)), ((nb074_alpha_dummy_131), (nb074_alpha_dummy_133 x)), ((nb074_alpha_dummy_132), (nb074_alpha_dummy_134 x)), ((nb074_alpha_dummy_124), (nb074_alpha_dummy_126 x)), ((nb074_alpha_dummy_123), (nb074_alpha_dummy_125 x)), ((nb074_alpha_dummy_129), (nb074_alpha_dummy_130 x)), ((nb074_alpha_dummy_127), (nb074_alpha_dummy_128 x)), ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb074_compact_envfresh_0023 x)

theorem nb074_wpp_notmem_0340 : (nb074_alpha_dummy_139) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_139, fv_syn_c0] using (nb074_compact_fv_empty_0094)

theorem nb074_wpp_notmem_0341 (x : Var) : (nb074_alpha_dummy_142 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_142, fv_syn_c0] using (nb074_compact_fv_empty_0095 x)

theorem nb074_wpp_notmem_0342 : (nb074_alpha_dummy_138) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_138, fv_syn_c0] using (nb074_compact_fv_empty_0096)

theorem nb074_wpp_notmem_0343 (x : Var) : (nb074_alpha_dummy_141 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_141, fv_syn_c0] using (nb074_compact_fv_empty_0097 x)

theorem nb074_wpp_notmem_0344 : (nb074_alpha_dummy_137) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_137, fv_syn_c0] using (nb074_compact_fv_empty_0098)

theorem nb074_wpp_notmem_0345 (x : Var) : (nb074_alpha_dummy_140 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_140, fv_syn_c0] using (nb074_compact_fv_empty_0099 x)

theorem nb074_wpp_notmem_0346 : (nb074_alpha_dummy_135) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_135, fv_syn_c0] using (nb074_compact_fv_empty_0100)

theorem nb074_wpp_notmem_0347 (x : Var) : (nb074_alpha_dummy_136 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_136, fv_syn_c0] using (nb074_compact_fv_empty_0101 x)

theorem nb074_wpp_notmem_0348 : (nb074_alpha_dummy_131) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_131, fv_syn_c0] using (nb074_compact_fv_empty_0102)

theorem nb074_wpp_notmem_0349 (x : Var) : (nb074_alpha_dummy_133 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_133, fv_syn_c0] using (nb074_compact_fv_empty_0103 x)

theorem nb074_wpp_notmem_0350 : (nb074_alpha_dummy_132) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_132, fv_syn_c0] using (nb074_compact_fv_empty_0104)

theorem nb074_wpp_notmem_0351 (x : Var) : (nb074_alpha_dummy_134 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_134, fv_syn_c0] using (nb074_compact_fv_empty_0105 x)

theorem nb074_wpp_notmem_0352 : (nb074_alpha_dummy_124) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_124, fv_syn_c0] using (nb074_compact_fv_empty_0106)

theorem nb074_wpp_notmem_0353 (x : Var) : (nb074_alpha_dummy_126 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_126, fv_syn_c0] using (nb074_compact_fv_empty_0107 x)

theorem nb074_wpp_notmem_0354 : (nb074_alpha_dummy_123) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_123, fv_syn_c0] using (nb074_compact_fv_empty_0108)

theorem nb074_wpp_notmem_0355 (x : Var) : (nb074_alpha_dummy_125 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_125, fv_syn_c0] using (nb074_compact_fv_empty_0109 x)

theorem nb074_wpp_notmem_0356 : (nb074_alpha_dummy_129) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_129, fv_syn_c0] using (nb074_compact_fv_empty_0110)

theorem nb074_wpp_notmem_0357 (x : Var) : (nb074_alpha_dummy_130 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_130, fv_syn_c0] using (nb074_compact_fv_empty_0111 x)

theorem nb074_wpp_notmem_0358 : (nb074_alpha_dummy_127) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_127, fv_syn_c0] using (nb074_compact_fv_empty_0112)

theorem nb074_wpp_notmem_0359 (x : Var) : (nb074_alpha_dummy_128 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_128, fv_syn_c0] using (nb074_compact_fv_empty_0113 x)

theorem nb074_compact_envfresh_0024 (x : Var) : TEnvFresh [((nb074_alpha_dummy_139), (nb074_alpha_dummy_142 x)), ((nb074_alpha_dummy_138), (nb074_alpha_dummy_141 x)), ((nb074_alpha_dummy_137), (nb074_alpha_dummy_140 x)), ((nb074_alpha_dummy_135), (nb074_alpha_dummy_136 x)), ((nb074_alpha_dummy_131), (nb074_alpha_dummy_133 x)), ((nb074_alpha_dummy_132), (nb074_alpha_dummy_134 x)), ((nb074_alpha_dummy_124), (nb074_alpha_dummy_126 x)), ((nb074_alpha_dummy_123), (nb074_alpha_dummy_125 x)), ((nb074_alpha_dummy_129), (nb074_alpha_dummy_130 x)), ((nb074_alpha_dummy_127), (nb074_alpha_dummy_128 x)), ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb074_alpha_dummy_139) (nb074_alpha_dummy_142 x) (nb074_wpp_notmem_0340) (nb074_wpp_notmem_0341 x) (TEnvFresh.consFresh (nb074_alpha_dummy_138) (nb074_alpha_dummy_141 x) (nb074_wpp_notmem_0342) (nb074_wpp_notmem_0343 x) (TEnvFresh.consFresh (nb074_alpha_dummy_137) (nb074_alpha_dummy_140 x) (nb074_wpp_notmem_0344) (nb074_wpp_notmem_0345 x) (TEnvFresh.consFresh (nb074_alpha_dummy_135) (nb074_alpha_dummy_136 x) (nb074_wpp_notmem_0346) (nb074_wpp_notmem_0347 x) (TEnvFresh.consFresh (nb074_alpha_dummy_131) (nb074_alpha_dummy_133 x) (nb074_wpp_notmem_0348) (nb074_wpp_notmem_0349 x) (TEnvFresh.consFresh (nb074_alpha_dummy_132) (nb074_alpha_dummy_134 x) (nb074_wpp_notmem_0350) (nb074_wpp_notmem_0351 x) (TEnvFresh.consFresh (nb074_alpha_dummy_124) (nb074_alpha_dummy_126 x) (nb074_wpp_notmem_0352) (nb074_wpp_notmem_0353 x) (TEnvFresh.consFresh (nb074_alpha_dummy_123) (nb074_alpha_dummy_125 x) (nb074_wpp_notmem_0354) (nb074_wpp_notmem_0355 x) (TEnvFresh.consFresh (nb074_alpha_dummy_129) (nb074_alpha_dummy_130 x) (nb074_wpp_notmem_0356) (nb074_wpp_notmem_0357 x) (TEnvFresh.consFresh (nb074_alpha_dummy_127) (nb074_alpha_dummy_128 x) (nb074_wpp_notmem_0358) (nb074_wpp_notmem_0359 x) (TEnvFresh.consFresh (nb074_alpha_dummy_082) (nb074_alpha_dummy_084 x) (nb074_wpp_notmem_0260) (nb074_wpp_notmem_0261 x) (TEnvFresh.consFresh (nb074_alpha_dummy_081) (nb074_alpha_dummy_083 x) (nb074_wpp_notmem_0262) (nb074_wpp_notmem_0263 x) (TEnvFresh.consFresh (nb074_alpha_dummy_085) (nb074_alpha_dummy_086 x) (nb074_wpp_notmem_0264) (nb074_wpp_notmem_0265 x) (TEnvFresh.consFresh (nb074_alpha_dummy_042) (nb074_alpha_dummy_044 x) (nb074_wpp_notmem_0160) (nb074_wpp_notmem_0161 x) (TEnvFresh.consFresh (nb074_alpha_dummy_041) (nb074_alpha_dummy_043 x) (nb074_wpp_notmem_0162) (nb074_wpp_notmem_0163 x) (TEnvFresh.consFresh (nb074_alpha_dummy_001) (nb074_alpha_dummy_002 x) (nb074_wpp_notmem_0046) (nb074_wpp_notmem_0047 x) (TEnvFresh.consFresh (nb074_alpha_dummy_000) x (nb074_wpp_notmem_0048) (nb074_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb074_alpha_dummy_003) (nb074_alpha_dummy_004 x) (nb074_wpp_notmem_0050) (nb074_wpp_notmem_0051 x) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))

noncomputable def nb074_wpp_refl_0024 (x : Var) : TReflOn [((nb074_alpha_dummy_139), (nb074_alpha_dummy_142 x)), ((nb074_alpha_dummy_138), (nb074_alpha_dummy_141 x)), ((nb074_alpha_dummy_137), (nb074_alpha_dummy_140 x)), ((nb074_alpha_dummy_135), (nb074_alpha_dummy_136 x)), ((nb074_alpha_dummy_131), (nb074_alpha_dummy_133 x)), ((nb074_alpha_dummy_132), (nb074_alpha_dummy_134 x)), ((nb074_alpha_dummy_124), (nb074_alpha_dummy_126 x)), ((nb074_alpha_dummy_123), (nb074_alpha_dummy_125 x)), ((nb074_alpha_dummy_129), (nb074_alpha_dummy_130 x)), ((nb074_alpha_dummy_127), (nb074_alpha_dummy_128 x)), ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb074_compact_envfresh_0024 x)

theorem nb074_wpp_notmem_0360 : (nb074_alpha_dummy_135) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_135, fv_syn_cnnc] using (nb074_compact_fv_empty_0100)

theorem nb074_wpp_notmem_0361 (x : Var) : (nb074_alpha_dummy_136 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_136, fv_syn_cnnc] using (nb074_compact_fv_empty_0101 x)

theorem nb074_wpp_notmem_0362 : (nb074_alpha_dummy_131) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_131, fv_syn_cnnc] using (nb074_compact_fv_empty_0102)

theorem nb074_wpp_notmem_0363 (x : Var) : (nb074_alpha_dummy_133 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_133, fv_syn_cnnc] using (nb074_compact_fv_empty_0103 x)

theorem nb074_wpp_notmem_0364 : (nb074_alpha_dummy_132) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_132, fv_syn_cnnc] using (nb074_compact_fv_empty_0104)

theorem nb074_wpp_notmem_0365 (x : Var) : (nb074_alpha_dummy_134 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_134, fv_syn_cnnc] using (nb074_compact_fv_empty_0105 x)

theorem nb074_wpp_notmem_0366 : (nb074_alpha_dummy_124) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_124, fv_syn_cnnc] using (nb074_compact_fv_empty_0106)

theorem nb074_wpp_notmem_0367 (x : Var) : (nb074_alpha_dummy_126 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_126, fv_syn_cnnc] using (nb074_compact_fv_empty_0107 x)

theorem nb074_wpp_notmem_0368 : (nb074_alpha_dummy_123) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_123, fv_syn_cnnc] using (nb074_compact_fv_empty_0108)

theorem nb074_wpp_notmem_0369 (x : Var) : (nb074_alpha_dummy_125 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_125, fv_syn_cnnc] using (nb074_compact_fv_empty_0109 x)

theorem nb074_wpp_notmem_0370 : (nb074_alpha_dummy_129) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_129, fv_syn_cnnc] using (nb074_compact_fv_empty_0110)

theorem nb074_wpp_notmem_0371 (x : Var) : (nb074_alpha_dummy_130 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_130, fv_syn_cnnc] using (nb074_compact_fv_empty_0111 x)

theorem nb074_wpp_notmem_0372 : (nb074_alpha_dummy_127) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_127, fv_syn_cnnc] using (nb074_compact_fv_empty_0112)

theorem nb074_wpp_notmem_0373 (x : Var) : (nb074_alpha_dummy_128 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_128, fv_syn_cnnc] using (nb074_compact_fv_empty_0113 x)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
