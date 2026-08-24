import NAR4C090C001Part027

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

theorem nb090_compact_envfresh_0019 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_109 A), (nb090_alpha_dummy_112 h)), ((nb090_alpha_dummy_108 A), (nb090_alpha_dummy_111 h)), ((nb090_alpha_dummy_107 A), (nb090_alpha_dummy_110 h)), ((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)), ((nb090_alpha_dummy_101 A), (nb090_alpha_dummy_103 h)), ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)), ((nb090_alpha_dummy_127 A), (nb090_alpha_dummy_128 h)), ((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)), ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)), ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)), ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)), ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_109 A) (nb090_alpha_dummy_112 h) (nb090_wpp_notmem_0264 A) (nb090_wpp_notmem_0265 h) (TEnvFresh.consFresh (nb090_alpha_dummy_108 A) (nb090_alpha_dummy_111 h) (nb090_wpp_notmem_0266 A) (nb090_wpp_notmem_0267 h) (TEnvFresh.consFresh (nb090_alpha_dummy_107 A) (nb090_alpha_dummy_110 h) (nb090_wpp_notmem_0268 A) (nb090_wpp_notmem_0269 h) (TEnvFresh.consFresh (nb090_alpha_dummy_105 A) (nb090_alpha_dummy_106 h) (nb090_wpp_notmem_0270 A) (nb090_wpp_notmem_0271 h) (TEnvFresh.consFresh (nb090_alpha_dummy_101 A) (nb090_alpha_dummy_103 h) (nb090_wpp_notmem_0272 A) (nb090_wpp_notmem_0273 h) (TEnvFresh.consFresh (nb090_alpha_dummy_102 A) (nb090_alpha_dummy_104 h) (nb090_wpp_notmem_0274 A) (nb090_wpp_notmem_0275 h) (TEnvFresh.consFresh (nb090_alpha_dummy_127 A) (nb090_alpha_dummy_128 h) (nb090_wpp_notmem_0308 A) (nb090_wpp_notmem_0309 h) (TEnvFresh.consFresh (nb090_alpha_dummy_125 A) (nb090_alpha_dummy_126 h) (nb090_wpp_notmem_0310 A) (nb090_wpp_notmem_0311 h) (TEnvFresh.consFresh (nb090_alpha_dummy_094 A) (nb090_alpha_dummy_096 h) (nb090_wpp_notmem_0276 A) (nb090_wpp_notmem_0277 h) (TEnvFresh.consFresh (nb090_alpha_dummy_093 A) (nb090_alpha_dummy_095 h) (nb090_wpp_notmem_0278 A) (nb090_wpp_notmem_0279 h) (TEnvFresh.consFresh (nb090_alpha_dummy_123 A) (nb090_alpha_dummy_124 h) (nb090_wpp_notmem_0312 A) (nb090_wpp_notmem_0313 h) (TEnvFresh.consFresh (nb090_alpha_dummy_097 A) (nb090_alpha_dummy_098 h) (nb090_wpp_notmem_0282 A) (nb090_wpp_notmem_0283 h) (TEnvFresh.consFresh (nb090_alpha_dummy_051 A) (nb090_alpha_dummy_054 h) (nb090_wpp_notmem_0284 A) (nb090_wpp_notmem_0285 h) (TEnvFresh.consFresh (nb090_alpha_dummy_050 A) (nb090_alpha_dummy_053 h) (nb090_wpp_notmem_0164 A) (nb090_wpp_notmem_0165 h) (TEnvFresh.consFresh (nb090_alpha_dummy_049 A) (nb090_alpha_dummy_052 h) (nb090_wpp_notmem_0166 A) (nb090_wpp_notmem_0167 h) (TEnvFresh.consFresh (nb090_alpha_dummy_055 A) (nb090_alpha_dummy_056 h) (nb090_wpp_notmem_0168 A) (nb090_wpp_notmem_0169 h) (TEnvFresh.consFresh (nb090_alpha_dummy_047 A) (nb090_alpha_dummy_048 h) (nb090_wpp_notmem_0170 A) (nb090_wpp_notmem_0171 h) (TEnvFresh.consFresh (nb090_alpha_dummy_045 A) (nb090_alpha_dummy_046 h) (nb090_wpp_notmem_0172 A) (nb090_wpp_notmem_0173 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0174 A) (nb090_wpp_notmem_0175 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0046 A) (nb090_wpp_notmem_0047 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0048 A) (nb090_wpp_notmem_0049 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0050 A) (nb090_wpp_notmem_0051 v u A h) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))))

noncomputable def nb090_wpp_refl_0019 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_109 A), (nb090_alpha_dummy_112 h)), ((nb090_alpha_dummy_108 A), (nb090_alpha_dummy_111 h)), ((nb090_alpha_dummy_107 A), (nb090_alpha_dummy_110 h)), ((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)), ((nb090_alpha_dummy_101 A), (nb090_alpha_dummy_103 h)), ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)), ((nb090_alpha_dummy_127 A), (nb090_alpha_dummy_128 h)), ((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)), ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)), ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)), ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)), ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0019 v u A h)

theorem nb090_wpp_notmem_0314 (A : Class) : (nb090_alpha_dummy_127 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_127, fv_syn_cnnc] using (nb090_compact_fv_empty_0092 A)

theorem nb090_wpp_notmem_0315 (h : Var) : (nb090_alpha_dummy_128 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_128, fv_syn_cnnc] using (nb090_compact_fv_empty_0093 h)

theorem nb090_wpp_notmem_0316 (A : Class) : (nb090_alpha_dummy_125 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_125, fv_syn_cnnc] using (nb090_compact_fv_empty_0094 A)

theorem nb090_wpp_notmem_0317 (h : Var) : (nb090_alpha_dummy_126 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_126, fv_syn_cnnc] using (nb090_compact_fv_empty_0095 h)

theorem nb090_wpp_notmem_0318 (A : Class) : (nb090_alpha_dummy_123 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_123, fv_syn_cnnc] using (nb090_compact_fv_empty_0096 A)

theorem nb090_wpp_notmem_0319 (h : Var) : (nb090_alpha_dummy_124 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_124, fv_syn_cnnc] using (nb090_compact_fv_empty_0097 h)

theorem nb090_compact_envfresh_0020 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)), ((nb090_alpha_dummy_101 A), (nb090_alpha_dummy_103 h)), ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)), ((nb090_alpha_dummy_127 A), (nb090_alpha_dummy_128 h)), ((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)), ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)), ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)), ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)), ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_105 A) (nb090_alpha_dummy_106 h) (nb090_wpp_notmem_0286 A) (nb090_wpp_notmem_0287 h) (TEnvFresh.consFresh (nb090_alpha_dummy_101 A) (nb090_alpha_dummy_103 h) (nb090_wpp_notmem_0288 A) (nb090_wpp_notmem_0289 h) (TEnvFresh.consFresh (nb090_alpha_dummy_102 A) (nb090_alpha_dummy_104 h) (nb090_wpp_notmem_0290 A) (nb090_wpp_notmem_0291 h) (TEnvFresh.consFresh (nb090_alpha_dummy_127 A) (nb090_alpha_dummy_128 h) (nb090_wpp_notmem_0314 A) (nb090_wpp_notmem_0315 h) (TEnvFresh.consFresh (nb090_alpha_dummy_125 A) (nb090_alpha_dummy_126 h) (nb090_wpp_notmem_0316 A) (nb090_wpp_notmem_0317 h) (TEnvFresh.consFresh (nb090_alpha_dummy_094 A) (nb090_alpha_dummy_096 h) (nb090_wpp_notmem_0292 A) (nb090_wpp_notmem_0293 h) (TEnvFresh.consFresh (nb090_alpha_dummy_093 A) (nb090_alpha_dummy_095 h) (nb090_wpp_notmem_0294 A) (nb090_wpp_notmem_0295 h) (TEnvFresh.consFresh (nb090_alpha_dummy_123 A) (nb090_alpha_dummy_124 h) (nb090_wpp_notmem_0318 A) (nb090_wpp_notmem_0319 h) (TEnvFresh.consFresh (nb090_alpha_dummy_097 A) (nb090_alpha_dummy_098 h) (nb090_wpp_notmem_0298 A) (nb090_wpp_notmem_0299 h) (TEnvFresh.consFresh (nb090_alpha_dummy_051 A) (nb090_alpha_dummy_054 h) (nb090_wpp_notmem_0300 A) (nb090_wpp_notmem_0301 h) (TEnvFresh.consFresh (nb090_alpha_dummy_050 A) (nb090_alpha_dummy_053 h) (nb090_wpp_notmem_0190 A) (nb090_wpp_notmem_0191 h) (TEnvFresh.consFresh (nb090_alpha_dummy_049 A) (nb090_alpha_dummy_052 h) (nb090_wpp_notmem_0192 A) (nb090_wpp_notmem_0193 h) (TEnvFresh.consFresh (nb090_alpha_dummy_055 A) (nb090_alpha_dummy_056 h) (nb090_wpp_notmem_0194 A) (nb090_wpp_notmem_0195 h) (TEnvFresh.consFresh (nb090_alpha_dummy_047 A) (nb090_alpha_dummy_048 h) (nb090_wpp_notmem_0196 A) (nb090_wpp_notmem_0197 h) (TEnvFresh.consFresh (nb090_alpha_dummy_045 A) (nb090_alpha_dummy_046 h) (nb090_wpp_notmem_0198 A) (nb090_wpp_notmem_0199 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0200 A) (nb090_wpp_notmem_0201 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0066 A) (nb090_wpp_notmem_0067 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0068 A) (nb090_wpp_notmem_0069 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0070 A) (nb090_wpp_notmem_0071 v u A h) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))))

noncomputable def nb090_wpp_refl_0020 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)), ((nb090_alpha_dummy_101 A), (nb090_alpha_dummy_103 h)), ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)), ((nb090_alpha_dummy_127 A), (nb090_alpha_dummy_128 h)), ((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)), ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)), ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)), ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)), ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0020 v u A h)

noncomputable def nb090_split_alpha_0004 (v : Var) (u : Var) (A : Class) (h : Var) : TAlphaWff [((nb090_alpha_dummy_127 A), (nb090_alpha_dummy_128 h)), ((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)), ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)), ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)), ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)), ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_127 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))) (Wff.neg (Wff.classMem (Class.cv (nb090_alpha_dummy_127 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))))) (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_128 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))) (Wff.neg (Wff.classMem (Class.cv (nb090_alpha_dummy_128 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0090 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0091 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0090 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0091 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0120 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0121 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0118 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0119 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_094 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_096 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0094 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0095 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0094 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0095 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0092 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0093 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_109 A), (nb090_alpha_dummy_112 h)), ((nb090_alpha_dummy_108 A), (nb090_alpha_dummy_111 h)), ((nb090_alpha_dummy_107 A), (nb090_alpha_dummy_110 h)), ((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)), ((nb090_alpha_dummy_101 A), (nb090_alpha_dummy_103 h)), ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)), ((nb090_alpha_dummy_127 A), (nb090_alpha_dummy_128 h)), ((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)), ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)), ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)), ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)), ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0018 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0098 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0099 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0096 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0097 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0102 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0103 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0100 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0101 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0098 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0099 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0096 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0097 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0102 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0103 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0100 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0101 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_109 A), (nb090_alpha_dummy_112 h)), ((nb090_alpha_dummy_108 A), (nb090_alpha_dummy_111 h)), ((nb090_alpha_dummy_107 A), (nb090_alpha_dummy_110 h)), ((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)), ((nb090_alpha_dummy_101 A), (nb090_alpha_dummy_103 h)), ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)), ((nb090_alpha_dummy_127 A), (nb090_alpha_dummy_128 h)), ((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)), ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)), ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)), ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)), ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0019 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0106 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0107 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0104 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0105 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0106 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0107 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0104 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0105 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0110 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0111 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0108 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0109 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0110 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0111 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0108 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0109 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0092 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0093 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)), ((nb090_alpha_dummy_101 A), (nb090_alpha_dummy_103 h)), ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)), ((nb090_alpha_dummy_127 A), (nb090_alpha_dummy_128 h)), ((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)), ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)), ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)), ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)), ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0020 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0092 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0093 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0092 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0093 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)), ((nb090_alpha_dummy_101 A), (nb090_alpha_dummy_103 h)), ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)), ((nb090_alpha_dummy_127 A), (nb090_alpha_dummy_128 h)), ((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)), ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)), ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)), ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)), ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0020 v u A h)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0090 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0091 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0090 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0091 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0120 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0121 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0118 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0119 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_094 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_096 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0094 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0095 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0094 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0095 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0092 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0093 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_109 A), (nb090_alpha_dummy_112 h)), ((nb090_alpha_dummy_108 A), (nb090_alpha_dummy_111 h)), ((nb090_alpha_dummy_107 A), (nb090_alpha_dummy_110 h)), ((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)), ((nb090_alpha_dummy_101 A), (nb090_alpha_dummy_103 h)), ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)), ((nb090_alpha_dummy_127 A), (nb090_alpha_dummy_128 h)), ((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)), ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)), ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)), ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)), ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0018 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0098 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0099 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0096 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0097 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0102 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0103 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0100 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0101 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0098 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0099 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0096 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0097 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0102 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0103 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0100 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0101 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_109 A), (nb090_alpha_dummy_112 h)), ((nb090_alpha_dummy_108 A), (nb090_alpha_dummy_111 h)), ((nb090_alpha_dummy_107 A), (nb090_alpha_dummy_110 h)), ((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)), ((nb090_alpha_dummy_101 A), (nb090_alpha_dummy_103 h)), ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)), ((nb090_alpha_dummy_127 A), (nb090_alpha_dummy_128 h)), ((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)), ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)), ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)), ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)), ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0019 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0106 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0107 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0104 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0105 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0106 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0107 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0104 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0105 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0110 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0111 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0108 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0109 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0110 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0111 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0108 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0109 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0092 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0093 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)), ((nb090_alpha_dummy_101 A), (nb090_alpha_dummy_103 h)), ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)), ((nb090_alpha_dummy_127 A), (nb090_alpha_dummy_128 h)), ((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)), ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)), ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)), ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)), ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0020 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0092 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0093 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0092 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0093 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)), ((nb090_alpha_dummy_101 A), (nb090_alpha_dummy_103 h)), ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)), ((nb090_alpha_dummy_127 A), (nb090_alpha_dummy_128 h)), ((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)), ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)), ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)), ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)), ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0020 v u A h))))))))))))))))))))

theorem nb090_wpp_notmem_0320 (A : Class) : (nb090_alpha_dummy_125 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_125, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0094 A)

theorem nb090_wpp_notmem_0321 (h : Var) : (nb090_alpha_dummy_126 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_126, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0095 h)

theorem nb090_wpp_notmem_0322 (A : Class) : (nb090_alpha_dummy_094 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_094, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0082 A)

theorem nb090_wpp_notmem_0323 (h : Var) : (nb090_alpha_dummy_096 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_096, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0083 h)

theorem nb090_wpp_notmem_0324 (A : Class) : (nb090_alpha_dummy_093 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_093, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0084 A)

theorem nb090_wpp_notmem_0325 (h : Var) : (nb090_alpha_dummy_095 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_095, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0085 h)

theorem nb090_wpp_notmem_0326 (A : Class) : (nb090_alpha_dummy_123 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_123, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0096 A)

theorem nb090_wpp_notmem_0327 (h : Var) : (nb090_alpha_dummy_124 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_124, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0097 h)

theorem nb090_wpp_notmem_0328 (A : Class) : (nb090_alpha_dummy_097 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_097, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0088 A)

theorem nb090_wpp_notmem_0329 (h : Var) : (nb090_alpha_dummy_098 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_098, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0089 h)

theorem nb090_wpp_notmem_0330 (A : Class) : (nb090_alpha_dummy_051 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_051, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0090 A)

theorem nb090_wpp_notmem_0331 (h : Var) : (nb090_alpha_dummy_054 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_054, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0091 h)

theorem nb090_compact_envfresh_0021 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)), ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)), ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)), ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)), ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_125 A) (nb090_alpha_dummy_126 h) (nb090_wpp_notmem_0320 A) (nb090_wpp_notmem_0321 h) (TEnvFresh.consFresh (nb090_alpha_dummy_094 A) (nb090_alpha_dummy_096 h) (nb090_wpp_notmem_0322 A) (nb090_wpp_notmem_0323 h) (TEnvFresh.consFresh (nb090_alpha_dummy_093 A) (nb090_alpha_dummy_095 h) (nb090_wpp_notmem_0324 A) (nb090_wpp_notmem_0325 h) (TEnvFresh.consFresh (nb090_alpha_dummy_123 A) (nb090_alpha_dummy_124 h) (nb090_wpp_notmem_0326 A) (nb090_wpp_notmem_0327 h) (TEnvFresh.consFresh (nb090_alpha_dummy_097 A) (nb090_alpha_dummy_098 h) (nb090_wpp_notmem_0328 A) (nb090_wpp_notmem_0329 h) (TEnvFresh.consFresh (nb090_alpha_dummy_051 A) (nb090_alpha_dummy_054 h) (nb090_wpp_notmem_0330 A) (nb090_wpp_notmem_0331 h) (TEnvFresh.consFresh (nb090_alpha_dummy_050 A) (nb090_alpha_dummy_053 h) (nb090_wpp_notmem_0230 A) (nb090_wpp_notmem_0231 h) (TEnvFresh.consFresh (nb090_alpha_dummy_049 A) (nb090_alpha_dummy_052 h) (nb090_wpp_notmem_0232 A) (nb090_wpp_notmem_0233 h) (TEnvFresh.consFresh (nb090_alpha_dummy_055 A) (nb090_alpha_dummy_056 h) (nb090_wpp_notmem_0234 A) (nb090_wpp_notmem_0235 h) (TEnvFresh.consFresh (nb090_alpha_dummy_047 A) (nb090_alpha_dummy_048 h) (nb090_wpp_notmem_0236 A) (nb090_wpp_notmem_0237 h) (TEnvFresh.consFresh (nb090_alpha_dummy_045 A) (nb090_alpha_dummy_046 h) (nb090_wpp_notmem_0238 A) (nb090_wpp_notmem_0239 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0240 A) (nb090_wpp_notmem_0241 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0100 A) (nb090_wpp_notmem_0101 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0102 A) (nb090_wpp_notmem_0103 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0104 A) (nb090_wpp_notmem_0105 v u A h) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))))

noncomputable def nb090_wpp_refl_0021 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)), ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)), ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)), ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)), ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0021 v u A h)

theorem nb090_compact_fv_empty_0098 (A : Class) : (nb090_alpha_dummy_151 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0332 (A : Class) : (nb090_alpha_dummy_151 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_151, fv_syn_c1c] using (nb090_compact_fv_empty_0098 A)

theorem nb090_compact_fv_empty_0099 (h : Var) : (nb090_alpha_dummy_154 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0333 (h : Var) : (nb090_alpha_dummy_154 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_154, fv_syn_c1c] using (nb090_compact_fv_empty_0099 h)

theorem nb090_compact_fv_empty_0100 (A : Class) : (nb090_alpha_dummy_150 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0334 (A : Class) : (nb090_alpha_dummy_150 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_150, fv_syn_c1c] using (nb090_compact_fv_empty_0100 A)

theorem nb090_compact_fv_empty_0101 (h : Var) : (nb090_alpha_dummy_153 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0335 (h : Var) : (nb090_alpha_dummy_153 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_153, fv_syn_c1c] using (nb090_compact_fv_empty_0101 h)

theorem nb090_compact_fv_empty_0102 (A : Class) : (nb090_alpha_dummy_149 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0336 (A : Class) : (nb090_alpha_dummy_149 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_149, fv_syn_c1c] using (nb090_compact_fv_empty_0102 A)

theorem nb090_compact_fv_empty_0103 (h : Var) : (nb090_alpha_dummy_152 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0337 (h : Var) : (nb090_alpha_dummy_152 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_152, fv_syn_c1c] using (nb090_compact_fv_empty_0103 h)

theorem nb090_compact_fv_empty_0104 (A : Class) : (nb090_alpha_dummy_147 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0338 (A : Class) : (nb090_alpha_dummy_147 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_147, fv_syn_c1c] using (nb090_compact_fv_empty_0104 A)

theorem nb090_compact_fv_empty_0105 (h : Var) : (nb090_alpha_dummy_148 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0339 (h : Var) : (nb090_alpha_dummy_148 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_148, fv_syn_c1c] using (nb090_compact_fv_empty_0105 h)

theorem nb090_compact_fv_empty_0106 (A : Class) : (nb090_alpha_dummy_143 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0340 (A : Class) : (nb090_alpha_dummy_143 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_143, fv_syn_c1c] using (nb090_compact_fv_empty_0106 A)

theorem nb090_compact_fv_empty_0107 (h : Var) : (nb090_alpha_dummy_145 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0341 (h : Var) : (nb090_alpha_dummy_145 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_145, fv_syn_c1c] using (nb090_compact_fv_empty_0107 h)

theorem nb090_compact_fv_empty_0108 (A : Class) : (nb090_alpha_dummy_144 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0342 (A : Class) : (nb090_alpha_dummy_144 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_144, fv_syn_c1c] using (nb090_compact_fv_empty_0108 A)

theorem nb090_compact_fv_empty_0109 (h : Var) : (nb090_alpha_dummy_146 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0343 (h : Var) : (nb090_alpha_dummy_146 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_146, fv_syn_c1c] using (nb090_compact_fv_empty_0109 h)

theorem nb090_compact_fv_empty_0110 (A : Class) : (nb090_alpha_dummy_136 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0344 (A : Class) : (nb090_alpha_dummy_136 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_136, fv_syn_c1c] using (nb090_compact_fv_empty_0110 A)

theorem nb090_compact_fv_empty_0111 (h : Var) : (nb090_alpha_dummy_138 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0345 (h : Var) : (nb090_alpha_dummy_138 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_138, fv_syn_c1c] using (nb090_compact_fv_empty_0111 h)

theorem nb090_compact_fv_empty_0112 (A : Class) : (nb090_alpha_dummy_135 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0346 (A : Class) : (nb090_alpha_dummy_135 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_135, fv_syn_c1c] using (nb090_compact_fv_empty_0112 A)

theorem nb090_compact_fv_empty_0113 (h : Var) : (nb090_alpha_dummy_137 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0347 (h : Var) : (nb090_alpha_dummy_137 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_137, fv_syn_c1c] using (nb090_compact_fv_empty_0113 h)

theorem nb090_compact_fv_empty_0114 (A : Class) : (nb090_alpha_dummy_141 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0348 (A : Class) : (nb090_alpha_dummy_141 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_141, fv_syn_c1c] using (nb090_compact_fv_empty_0114 A)

theorem nb090_compact_fv_empty_0115 (h : Var) : (nb090_alpha_dummy_142 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0349 (h : Var) : (nb090_alpha_dummy_142 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_142, fv_syn_c1c] using (nb090_compact_fv_empty_0115 h)

theorem nb090_compact_fv_empty_0116 (A : Class) : (nb090_alpha_dummy_139 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0350 (A : Class) : (nb090_alpha_dummy_139 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_139, fv_syn_c1c] using (nb090_compact_fv_empty_0116 A)

theorem nb090_compact_fv_empty_0117 (h : Var) : (nb090_alpha_dummy_140 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0351 (h : Var) : (nb090_alpha_dummy_140 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_140, fv_syn_c1c] using (nb090_compact_fv_empty_0117 h)

theorem nb090_compact_fv_empty_0118 (A : Class) : (nb090_alpha_dummy_130 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0352 (A : Class) : (nb090_alpha_dummy_130 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_130, fv_syn_c1c] using (nb090_compact_fv_empty_0118 A)

theorem nb090_compact_fv_empty_0119 (h : Var) : (nb090_alpha_dummy_132 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0353 (h : Var) : (nb090_alpha_dummy_132 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_132, fv_syn_c1c] using (nb090_compact_fv_empty_0119 h)

theorem nb090_compact_fv_empty_0120 (A : Class) : (nb090_alpha_dummy_129 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0354 (A : Class) : (nb090_alpha_dummy_129 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_129, fv_syn_c1c] using (nb090_compact_fv_empty_0120 A)

theorem nb090_compact_fv_empty_0121 (h : Var) : (nb090_alpha_dummy_131 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0355 (h : Var) : (nb090_alpha_dummy_131 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_131, fv_syn_c1c] using (nb090_compact_fv_empty_0121 h)

theorem nb090_compact_fv_empty_0122 (A : Class) : (nb090_alpha_dummy_133 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0356 (A : Class) : (nb090_alpha_dummy_133 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_133, fv_syn_c1c] using (nb090_compact_fv_empty_0122 A)

theorem nb090_compact_fv_empty_0123 (h : Var) : (nb090_alpha_dummy_134 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0357 (h : Var) : (nb090_alpha_dummy_134 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_134, fv_syn_c1c] using (nb090_compact_fv_empty_0123 h)

theorem nb090_compact_envfresh_0022 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A), (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)), ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_151 A) (nb090_alpha_dummy_154 h) (nb090_wpp_notmem_0332 A) (nb090_wpp_notmem_0333 h) (TEnvFresh.consFresh (nb090_alpha_dummy_150 A) (nb090_alpha_dummy_153 h) (nb090_wpp_notmem_0334 A) (nb090_wpp_notmem_0335 h) (TEnvFresh.consFresh (nb090_alpha_dummy_149 A) (nb090_alpha_dummy_152 h) (nb090_wpp_notmem_0336 A) (nb090_wpp_notmem_0337 h) (TEnvFresh.consFresh (nb090_alpha_dummy_147 A) (nb090_alpha_dummy_148 h) (nb090_wpp_notmem_0338 A) (nb090_wpp_notmem_0339 h) (TEnvFresh.consFresh (nb090_alpha_dummy_143 A) (nb090_alpha_dummy_145 h) (nb090_wpp_notmem_0340 A) (nb090_wpp_notmem_0341 h) (TEnvFresh.consFresh (nb090_alpha_dummy_144 A) (nb090_alpha_dummy_146 h) (nb090_wpp_notmem_0342 A) (nb090_wpp_notmem_0343 h) (TEnvFresh.consFresh (nb090_alpha_dummy_136 A) (nb090_alpha_dummy_138 h) (nb090_wpp_notmem_0344 A) (nb090_wpp_notmem_0345 h) (TEnvFresh.consFresh (nb090_alpha_dummy_135 A) (nb090_alpha_dummy_137 h) (nb090_wpp_notmem_0346 A) (nb090_wpp_notmem_0347 h) (TEnvFresh.consFresh (nb090_alpha_dummy_141 A) (nb090_alpha_dummy_142 h) (nb090_wpp_notmem_0348 A) (nb090_wpp_notmem_0349 h) (TEnvFresh.consFresh (nb090_alpha_dummy_139 A) (nb090_alpha_dummy_140 h) (nb090_wpp_notmem_0350 A) (nb090_wpp_notmem_0351 h) (TEnvFresh.consFresh (nb090_alpha_dummy_130 A) (nb090_alpha_dummy_132 h) (nb090_wpp_notmem_0352 A) (nb090_wpp_notmem_0353 h) (TEnvFresh.consFresh (nb090_alpha_dummy_129 A) (nb090_alpha_dummy_131 h) (nb090_wpp_notmem_0354 A) (nb090_wpp_notmem_0355 h) (TEnvFresh.consFresh (nb090_alpha_dummy_133 A) (nb090_alpha_dummy_134 h) (nb090_wpp_notmem_0356 A) (nb090_wpp_notmem_0357 h) (TEnvFresh.consFresh (nb090_alpha_dummy_051 A) (nb090_alpha_dummy_054 h) (nb090_wpp_notmem_0262 A) (nb090_wpp_notmem_0263 h) (TEnvFresh.consFresh (nb090_alpha_dummy_050 A) (nb090_alpha_dummy_053 h) (nb090_wpp_notmem_0132 A) (nb090_wpp_notmem_0133 h) (TEnvFresh.consFresh (nb090_alpha_dummy_049 A) (nb090_alpha_dummy_052 h) (nb090_wpp_notmem_0134 A) (nb090_wpp_notmem_0135 h) (TEnvFresh.consFresh (nb090_alpha_dummy_055 A) (nb090_alpha_dummy_056 h) (nb090_wpp_notmem_0136 A) (nb090_wpp_notmem_0137 h) (TEnvFresh.consFresh (nb090_alpha_dummy_047 A) (nb090_alpha_dummy_048 h) (nb090_wpp_notmem_0138 A) (nb090_wpp_notmem_0139 h) (TEnvFresh.consFresh (nb090_alpha_dummy_045 A) (nb090_alpha_dummy_046 h) (nb090_wpp_notmem_0140 A) (nb090_wpp_notmem_0141 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0142 A) (nb090_wpp_notmem_0143 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0020 A) (nb090_wpp_notmem_0021 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0022 A) (nb090_wpp_notmem_0023 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0024 A) (nb090_wpp_notmem_0025 v u A h) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))))))

noncomputable def nb090_wpp_refl_0022 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A), (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)), ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0022 v u A h)

theorem nb090_wpp_notmem_0358 (A : Class) : (nb090_alpha_dummy_151 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_151, fv_syn_c0] using (nb090_compact_fv_empty_0098 A)

theorem nb090_wpp_notmem_0359 (h : Var) : (nb090_alpha_dummy_154 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_154, fv_syn_c0] using (nb090_compact_fv_empty_0099 h)

theorem nb090_wpp_notmem_0360 (A : Class) : (nb090_alpha_dummy_150 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_150, fv_syn_c0] using (nb090_compact_fv_empty_0100 A)

theorem nb090_wpp_notmem_0361 (h : Var) : (nb090_alpha_dummy_153 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_153, fv_syn_c0] using (nb090_compact_fv_empty_0101 h)

theorem nb090_wpp_notmem_0362 (A : Class) : (nb090_alpha_dummy_149 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_149, fv_syn_c0] using (nb090_compact_fv_empty_0102 A)

theorem nb090_wpp_notmem_0363 (h : Var) : (nb090_alpha_dummy_152 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_152, fv_syn_c0] using (nb090_compact_fv_empty_0103 h)

theorem nb090_wpp_notmem_0364 (A : Class) : (nb090_alpha_dummy_147 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_147, fv_syn_c0] using (nb090_compact_fv_empty_0104 A)

theorem nb090_wpp_notmem_0365 (h : Var) : (nb090_alpha_dummy_148 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_148, fv_syn_c0] using (nb090_compact_fv_empty_0105 h)

theorem nb090_wpp_notmem_0366 (A : Class) : (nb090_alpha_dummy_143 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_143, fv_syn_c0] using (nb090_compact_fv_empty_0106 A)

theorem nb090_wpp_notmem_0367 (h : Var) : (nb090_alpha_dummy_145 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_145, fv_syn_c0] using (nb090_compact_fv_empty_0107 h)

theorem nb090_wpp_notmem_0368 (A : Class) : (nb090_alpha_dummy_144 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_144, fv_syn_c0] using (nb090_compact_fv_empty_0108 A)

theorem nb090_wpp_notmem_0369 (h : Var) : (nb090_alpha_dummy_146 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_146, fv_syn_c0] using (nb090_compact_fv_empty_0109 h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
