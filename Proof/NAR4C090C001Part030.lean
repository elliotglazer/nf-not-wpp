import NAR4C090C001Part029

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

noncomputable def nb090_wpp_refl_0026 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A), (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)), ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)), ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)), ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0026 v u A h)

theorem nb090_wpp_notmem_0416 (A : Class) : (nb090_alpha_dummy_169 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_169, fv_syn_cnnc] using (nb090_compact_fv_empty_0124 A)

theorem nb090_wpp_notmem_0417 (h : Var) : (nb090_alpha_dummy_170 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_170, fv_syn_cnnc] using (nb090_compact_fv_empty_0125 h)

theorem nb090_wpp_notmem_0418 (A : Class) : (nb090_alpha_dummy_167 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_167, fv_syn_cnnc] using (nb090_compact_fv_empty_0126 A)

theorem nb090_wpp_notmem_0419 (h : Var) : (nb090_alpha_dummy_168 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_168, fv_syn_cnnc] using (nb090_compact_fv_empty_0127 h)

theorem nb090_wpp_notmem_0420 (A : Class) : (nb090_alpha_dummy_165 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_165, fv_syn_cnnc] using (nb090_compact_fv_empty_0128 A)

theorem nb090_wpp_notmem_0421 (h : Var) : (nb090_alpha_dummy_166 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_166, fv_syn_cnnc] using (nb090_compact_fv_empty_0129 h)

theorem nb090_compact_envfresh_0027 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)), ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)), ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_147 A) (nb090_alpha_dummy_148 h) (nb090_wpp_notmem_0384 A) (nb090_wpp_notmem_0385 h) (TEnvFresh.consFresh (nb090_alpha_dummy_143 A) (nb090_alpha_dummy_145 h) (nb090_wpp_notmem_0386 A) (nb090_wpp_notmem_0387 h) (TEnvFresh.consFresh (nb090_alpha_dummy_144 A) (nb090_alpha_dummy_146 h) (nb090_wpp_notmem_0388 A) (nb090_wpp_notmem_0389 h) (TEnvFresh.consFresh (nb090_alpha_dummy_169 A) (nb090_alpha_dummy_170 h) (nb090_wpp_notmem_0416 A) (nb090_wpp_notmem_0417 h) (TEnvFresh.consFresh (nb090_alpha_dummy_167 A) (nb090_alpha_dummy_168 h) (nb090_wpp_notmem_0418 A) (nb090_wpp_notmem_0419 h) (TEnvFresh.consFresh (nb090_alpha_dummy_136 A) (nb090_alpha_dummy_138 h) (nb090_wpp_notmem_0390 A) (nb090_wpp_notmem_0391 h) (TEnvFresh.consFresh (nb090_alpha_dummy_135 A) (nb090_alpha_dummy_137 h) (nb090_wpp_notmem_0392 A) (nb090_wpp_notmem_0393 h) (TEnvFresh.consFresh (nb090_alpha_dummy_165 A) (nb090_alpha_dummy_166 h) (nb090_wpp_notmem_0420 A) (nb090_wpp_notmem_0421 h) (TEnvFresh.consFresh (nb090_alpha_dummy_139 A) (nb090_alpha_dummy_140 h) (nb090_wpp_notmem_0396 A) (nb090_wpp_notmem_0397 h) (TEnvFresh.consFresh (nb090_alpha_dummy_130 A) (nb090_alpha_dummy_132 h) (nb090_wpp_notmem_0398 A) (nb090_wpp_notmem_0399 h) (TEnvFresh.consFresh (nb090_alpha_dummy_129 A) (nb090_alpha_dummy_131 h) (nb090_wpp_notmem_0400 A) (nb090_wpp_notmem_0401 h) (TEnvFresh.consFresh (nb090_alpha_dummy_133 A) (nb090_alpha_dummy_134 h) (nb090_wpp_notmem_0402 A) (nb090_wpp_notmem_0403 h) (TEnvFresh.consFresh (nb090_alpha_dummy_051 A) (nb090_alpha_dummy_054 h) (nb090_wpp_notmem_0300 A) (nb090_wpp_notmem_0301 h) (TEnvFresh.consFresh (nb090_alpha_dummy_050 A) (nb090_alpha_dummy_053 h) (nb090_wpp_notmem_0190 A) (nb090_wpp_notmem_0191 h) (TEnvFresh.consFresh (nb090_alpha_dummy_049 A) (nb090_alpha_dummy_052 h) (nb090_wpp_notmem_0192 A) (nb090_wpp_notmem_0193 h) (TEnvFresh.consFresh (nb090_alpha_dummy_055 A) (nb090_alpha_dummy_056 h) (nb090_wpp_notmem_0194 A) (nb090_wpp_notmem_0195 h) (TEnvFresh.consFresh (nb090_alpha_dummy_047 A) (nb090_alpha_dummy_048 h) (nb090_wpp_notmem_0196 A) (nb090_wpp_notmem_0197 h) (TEnvFresh.consFresh (nb090_alpha_dummy_045 A) (nb090_alpha_dummy_046 h) (nb090_wpp_notmem_0198 A) (nb090_wpp_notmem_0199 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0200 A) (nb090_wpp_notmem_0201 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0066 A) (nb090_wpp_notmem_0067 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0068 A) (nb090_wpp_notmem_0069 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0070 A) (nb090_wpp_notmem_0071 v u A h) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))))))))

noncomputable def nb090_wpp_refl_0027 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)), ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)), ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0027 v u A h)

noncomputable def nb090_split_alpha_0006 (v : Var) (u : Var) (A : Class) (h : Var) : TAlphaWff [((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)), ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_169 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))) (Wff.neg (Wff.classMem (Class.cv (nb090_alpha_dummy_169 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))))) (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_170 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))) (Wff.neg (Wff.classMem (Class.cv (nb090_alpha_dummy_170 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0132 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0133 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0132 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0133 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0162 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0163 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0160 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0161 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_136 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_138 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0136 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0137 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0136 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0137 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0134 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0135 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A), (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)), ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)), ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)), ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0025 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0140 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0141 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0138 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0139 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0144 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0145 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0142 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0143 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0140 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0141 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0138 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0139 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0144 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0145 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0142 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0143 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A), (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)), ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)), ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)), ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0026 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0148 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0149 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0146 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0147 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0148 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0149 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0146 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0147 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0152 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0153 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0150 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0151 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0152 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0153 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0150 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0151 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0134 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0135 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)), ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)), ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0027 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0134 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0135 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0134 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0135 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)), ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)), ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0027 v u A h)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0132 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0133 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0132 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0133 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0162 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0163 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0160 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0161 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_136 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_138 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0136 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0137 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0136 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0137 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0134 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0135 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A), (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)), ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)), ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)), ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0025 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0140 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0141 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0138 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0139 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0144 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0145 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0142 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0143 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0140 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0141 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0138 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0139 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0144 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0145 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0142 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0143 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A), (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)), ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)), ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)), ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0026 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0148 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0149 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0146 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0147 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0148 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0149 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0146 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0147 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0152 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0153 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0150 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0151 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0152 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0153 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0150 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0151 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0134 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0135 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)), ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)), ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0027 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0134 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0135 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0134 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0135 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)), ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)), ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0027 v u A h))))))))))))))))))))

theorem nb090_wpp_notmem_0422 (A : Class) : (nb090_alpha_dummy_167 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_167, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0126 A)

theorem nb090_wpp_notmem_0423 (h : Var) : (nb090_alpha_dummy_168 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_168, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0127 h)

theorem nb090_wpp_notmem_0424 (A : Class) : (nb090_alpha_dummy_136 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_136, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0110 A)

theorem nb090_wpp_notmem_0425 (h : Var) : (nb090_alpha_dummy_138 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_138, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0111 h)

theorem nb090_wpp_notmem_0426 (A : Class) : (nb090_alpha_dummy_135 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_135, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0112 A)

theorem nb090_wpp_notmem_0427 (h : Var) : (nb090_alpha_dummy_137 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_137, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0113 h)

theorem nb090_wpp_notmem_0428 (A : Class) : (nb090_alpha_dummy_165 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_165, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0128 A)

theorem nb090_wpp_notmem_0429 (h : Var) : (nb090_alpha_dummy_166 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_166, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0129 h)

theorem nb090_wpp_notmem_0430 (A : Class) : (nb090_alpha_dummy_139 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_139, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0116 A)

theorem nb090_wpp_notmem_0431 (h : Var) : (nb090_alpha_dummy_140 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_140, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0117 h)

theorem nb090_wpp_notmem_0432 (A : Class) : (nb090_alpha_dummy_130 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_130, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0118 A)

theorem nb090_wpp_notmem_0433 (h : Var) : (nb090_alpha_dummy_132 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_132, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0119 h)

theorem nb090_wpp_notmem_0434 (A : Class) : (nb090_alpha_dummy_129 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_129, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0120 A)

theorem nb090_wpp_notmem_0435 (h : Var) : (nb090_alpha_dummy_131 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_131, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0121 h)

theorem nb090_wpp_notmem_0436 (A : Class) : (nb090_alpha_dummy_133 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_133, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0122 A)

theorem nb090_wpp_notmem_0437 (h : Var) : (nb090_alpha_dummy_134 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_134, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0123 h)

theorem nb090_compact_envfresh_0028 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_167 A) (nb090_alpha_dummy_168 h) (nb090_wpp_notmem_0422 A) (nb090_wpp_notmem_0423 h) (TEnvFresh.consFresh (nb090_alpha_dummy_136 A) (nb090_alpha_dummy_138 h) (nb090_wpp_notmem_0424 A) (nb090_wpp_notmem_0425 h) (TEnvFresh.consFresh (nb090_alpha_dummy_135 A) (nb090_alpha_dummy_137 h) (nb090_wpp_notmem_0426 A) (nb090_wpp_notmem_0427 h) (TEnvFresh.consFresh (nb090_alpha_dummy_165 A) (nb090_alpha_dummy_166 h) (nb090_wpp_notmem_0428 A) (nb090_wpp_notmem_0429 h) (TEnvFresh.consFresh (nb090_alpha_dummy_139 A) (nb090_alpha_dummy_140 h) (nb090_wpp_notmem_0430 A) (nb090_wpp_notmem_0431 h) (TEnvFresh.consFresh (nb090_alpha_dummy_130 A) (nb090_alpha_dummy_132 h) (nb090_wpp_notmem_0432 A) (nb090_wpp_notmem_0433 h) (TEnvFresh.consFresh (nb090_alpha_dummy_129 A) (nb090_alpha_dummy_131 h) (nb090_wpp_notmem_0434 A) (nb090_wpp_notmem_0435 h) (TEnvFresh.consFresh (nb090_alpha_dummy_133 A) (nb090_alpha_dummy_134 h) (nb090_wpp_notmem_0436 A) (nb090_wpp_notmem_0437 h) (TEnvFresh.consFresh (nb090_alpha_dummy_051 A) (nb090_alpha_dummy_054 h) (nb090_wpp_notmem_0330 A) (nb090_wpp_notmem_0331 h) (TEnvFresh.consFresh (nb090_alpha_dummy_050 A) (nb090_alpha_dummy_053 h) (nb090_wpp_notmem_0230 A) (nb090_wpp_notmem_0231 h) (TEnvFresh.consFresh (nb090_alpha_dummy_049 A) (nb090_alpha_dummy_052 h) (nb090_wpp_notmem_0232 A) (nb090_wpp_notmem_0233 h) (TEnvFresh.consFresh (nb090_alpha_dummy_055 A) (nb090_alpha_dummy_056 h) (nb090_wpp_notmem_0234 A) (nb090_wpp_notmem_0235 h) (TEnvFresh.consFresh (nb090_alpha_dummy_047 A) (nb090_alpha_dummy_048 h) (nb090_wpp_notmem_0236 A) (nb090_wpp_notmem_0237 h) (TEnvFresh.consFresh (nb090_alpha_dummy_045 A) (nb090_alpha_dummy_046 h) (nb090_wpp_notmem_0238 A) (nb090_wpp_notmem_0239 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0240 A) (nb090_wpp_notmem_0241 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0100 A) (nb090_wpp_notmem_0101 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0102 A) (nb090_wpp_notmem_0103 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0104 A) (nb090_wpp_notmem_0105 v u A h) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))))))))))

noncomputable def nb090_wpp_refl_0028 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0028 v u A h)

theorem nb090_compact_fv_empty_0130 (A : Class) : (nb090_alpha_dummy_187 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0438 (A : Class) : (nb090_alpha_dummy_187 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_187, fv_syn_c1c] using (nb090_compact_fv_empty_0130 A)

theorem nb090_compact_fv_empty_0131 (h : Var) : (nb090_alpha_dummy_190 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0439 (h : Var) : (nb090_alpha_dummy_190 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_190, fv_syn_c1c] using (nb090_compact_fv_empty_0131 h)

theorem nb090_compact_fv_empty_0132 (A : Class) : (nb090_alpha_dummy_186 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0440 (A : Class) : (nb090_alpha_dummy_186 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_186, fv_syn_c1c] using (nb090_compact_fv_empty_0132 A)

theorem nb090_compact_fv_empty_0133 (h : Var) : (nb090_alpha_dummy_189 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0441 (h : Var) : (nb090_alpha_dummy_189 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_189, fv_syn_c1c] using (nb090_compact_fv_empty_0133 h)

theorem nb090_compact_fv_empty_0134 (A : Class) : (nb090_alpha_dummy_185 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0442 (A : Class) : (nb090_alpha_dummy_185 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_185, fv_syn_c1c] using (nb090_compact_fv_empty_0134 A)

theorem nb090_compact_fv_empty_0135 (h : Var) : (nb090_alpha_dummy_188 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0443 (h : Var) : (nb090_alpha_dummy_188 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_188, fv_syn_c1c] using (nb090_compact_fv_empty_0135 h)

theorem nb090_compact_fv_empty_0136 (A : Class) : (nb090_alpha_dummy_183 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0444 (A : Class) : (nb090_alpha_dummy_183 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_183, fv_syn_c1c] using (nb090_compact_fv_empty_0136 A)

theorem nb090_compact_fv_empty_0137 (h : Var) : (nb090_alpha_dummy_184 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0445 (h : Var) : (nb090_alpha_dummy_184 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_184, fv_syn_c1c] using (nb090_compact_fv_empty_0137 h)

theorem nb090_compact_fv_empty_0138 (A : Class) : (nb090_alpha_dummy_179 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0446 (A : Class) : (nb090_alpha_dummy_179 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_179, fv_syn_c1c] using (nb090_compact_fv_empty_0138 A)

theorem nb090_compact_fv_empty_0139 (h : Var) : (nb090_alpha_dummy_181 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0447 (h : Var) : (nb090_alpha_dummy_181 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_181, fv_syn_c1c] using (nb090_compact_fv_empty_0139 h)

theorem nb090_compact_fv_empty_0140 (A : Class) : (nb090_alpha_dummy_180 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0448 (A : Class) : (nb090_alpha_dummy_180 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_180, fv_syn_c1c] using (nb090_compact_fv_empty_0140 A)

theorem nb090_compact_fv_empty_0141 (h : Var) : (nb090_alpha_dummy_182 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0449 (h : Var) : (nb090_alpha_dummy_182 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_182, fv_syn_c1c] using (nb090_compact_fv_empty_0141 h)

theorem nb090_compact_fv_empty_0142 (A : Class) : (nb090_alpha_dummy_172 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0450 (A : Class) : (nb090_alpha_dummy_172 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_172, fv_syn_c1c] using (nb090_compact_fv_empty_0142 A)

theorem nb090_compact_fv_empty_0143 (h : Var) : (nb090_alpha_dummy_174 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0451 (h : Var) : (nb090_alpha_dummy_174 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_174, fv_syn_c1c] using (nb090_compact_fv_empty_0143 h)

theorem nb090_compact_fv_empty_0144 (A : Class) : (nb090_alpha_dummy_171 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0452 (A : Class) : (nb090_alpha_dummy_171 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_171, fv_syn_c1c] using (nb090_compact_fv_empty_0144 A)

theorem nb090_compact_fv_empty_0145 (h : Var) : (nb090_alpha_dummy_173 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0453 (h : Var) : (nb090_alpha_dummy_173 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_173, fv_syn_c1c] using (nb090_compact_fv_empty_0145 h)

theorem nb090_compact_fv_empty_0146 (A : Class) : (nb090_alpha_dummy_177 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0454 (A : Class) : (nb090_alpha_dummy_177 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_177, fv_syn_c1c] using (nb090_compact_fv_empty_0146 A)

theorem nb090_compact_fv_empty_0147 (h : Var) : (nb090_alpha_dummy_178 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0455 (h : Var) : (nb090_alpha_dummy_178 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_178, fv_syn_c1c] using (nb090_compact_fv_empty_0147 h)

theorem nb090_compact_fv_empty_0148 (A : Class) : (nb090_alpha_dummy_175 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0456 (A : Class) : (nb090_alpha_dummy_175 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_175, fv_syn_c1c] using (nb090_compact_fv_empty_0148 A)

theorem nb090_compact_fv_empty_0149 (h : Var) : (nb090_alpha_dummy_176 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0457 (h : Var) : (nb090_alpha_dummy_176 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_176, fv_syn_c1c] using (nb090_compact_fv_empty_0149 h)

theorem nb090_compact_envfresh_0029 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_187 A), (nb090_alpha_dummy_190 h)), ((nb090_alpha_dummy_186 A), (nb090_alpha_dummy_189 h)), ((nb090_alpha_dummy_185 A), (nb090_alpha_dummy_188 h)), ((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)), ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)), ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)), ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_177 A), (nb090_alpha_dummy_178 h)), ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_187 A) (nb090_alpha_dummy_190 h) (nb090_wpp_notmem_0438 A) (nb090_wpp_notmem_0439 h) (TEnvFresh.consFresh (nb090_alpha_dummy_186 A) (nb090_alpha_dummy_189 h) (nb090_wpp_notmem_0440 A) (nb090_wpp_notmem_0441 h) (TEnvFresh.consFresh (nb090_alpha_dummy_185 A) (nb090_alpha_dummy_188 h) (nb090_wpp_notmem_0442 A) (nb090_wpp_notmem_0443 h) (TEnvFresh.consFresh (nb090_alpha_dummy_183 A) (nb090_alpha_dummy_184 h) (nb090_wpp_notmem_0444 A) (nb090_wpp_notmem_0445 h) (TEnvFresh.consFresh (nb090_alpha_dummy_179 A) (nb090_alpha_dummy_181 h) (nb090_wpp_notmem_0446 A) (nb090_wpp_notmem_0447 h) (TEnvFresh.consFresh (nb090_alpha_dummy_180 A) (nb090_alpha_dummy_182 h) (nb090_wpp_notmem_0448 A) (nb090_wpp_notmem_0449 h) (TEnvFresh.consFresh (nb090_alpha_dummy_172 A) (nb090_alpha_dummy_174 h) (nb090_wpp_notmem_0450 A) (nb090_wpp_notmem_0451 h) (TEnvFresh.consFresh (nb090_alpha_dummy_171 A) (nb090_alpha_dummy_173 h) (nb090_wpp_notmem_0452 A) (nb090_wpp_notmem_0453 h) (TEnvFresh.consFresh (nb090_alpha_dummy_177 A) (nb090_alpha_dummy_178 h) (nb090_wpp_notmem_0454 A) (nb090_wpp_notmem_0455 h) (TEnvFresh.consFresh (nb090_alpha_dummy_175 A) (nb090_alpha_dummy_176 h) (nb090_wpp_notmem_0456 A) (nb090_wpp_notmem_0457 h) (TEnvFresh.consFresh (nb090_alpha_dummy_130 A) (nb090_alpha_dummy_132 h) (nb090_wpp_notmem_0352 A) (nb090_wpp_notmem_0353 h) (TEnvFresh.consFresh (nb090_alpha_dummy_129 A) (nb090_alpha_dummy_131 h) (nb090_wpp_notmem_0354 A) (nb090_wpp_notmem_0355 h) (TEnvFresh.consFresh (nb090_alpha_dummy_133 A) (nb090_alpha_dummy_134 h) (nb090_wpp_notmem_0356 A) (nb090_wpp_notmem_0357 h) (TEnvFresh.consFresh (nb090_alpha_dummy_051 A) (nb090_alpha_dummy_054 h) (nb090_wpp_notmem_0262 A) (nb090_wpp_notmem_0263 h) (TEnvFresh.consFresh (nb090_alpha_dummy_050 A) (nb090_alpha_dummy_053 h) (nb090_wpp_notmem_0132 A) (nb090_wpp_notmem_0133 h) (TEnvFresh.consFresh (nb090_alpha_dummy_049 A) (nb090_alpha_dummy_052 h) (nb090_wpp_notmem_0134 A) (nb090_wpp_notmem_0135 h) (TEnvFresh.consFresh (nb090_alpha_dummy_055 A) (nb090_alpha_dummy_056 h) (nb090_wpp_notmem_0136 A) (nb090_wpp_notmem_0137 h) (TEnvFresh.consFresh (nb090_alpha_dummy_047 A) (nb090_alpha_dummy_048 h) (nb090_wpp_notmem_0138 A) (nb090_wpp_notmem_0139 h) (TEnvFresh.consFresh (nb090_alpha_dummy_045 A) (nb090_alpha_dummy_046 h) (nb090_wpp_notmem_0140 A) (nb090_wpp_notmem_0141 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0142 A) (nb090_wpp_notmem_0143 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0020 A) (nb090_wpp_notmem_0021 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0022 A) (nb090_wpp_notmem_0023 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0024 A) (nb090_wpp_notmem_0025 v u A h) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))))))

noncomputable def nb090_wpp_refl_0029 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_187 A), (nb090_alpha_dummy_190 h)), ((nb090_alpha_dummy_186 A), (nb090_alpha_dummy_189 h)), ((nb090_alpha_dummy_185 A), (nb090_alpha_dummy_188 h)), ((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)), ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)), ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)), ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_177 A), (nb090_alpha_dummy_178 h)), ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0029 v u A h)

theorem nb090_wpp_notmem_0458 (A : Class) : (nb090_alpha_dummy_187 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_187, fv_syn_c0] using (nb090_compact_fv_empty_0130 A)

theorem nb090_wpp_notmem_0459 (h : Var) : (nb090_alpha_dummy_190 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_190, fv_syn_c0] using (nb090_compact_fv_empty_0131 h)

theorem nb090_wpp_notmem_0460 (A : Class) : (nb090_alpha_dummy_186 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_186, fv_syn_c0] using (nb090_compact_fv_empty_0132 A)

theorem nb090_wpp_notmem_0461 (h : Var) : (nb090_alpha_dummy_189 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_189, fv_syn_c0] using (nb090_compact_fv_empty_0133 h)

theorem nb090_wpp_notmem_0462 (A : Class) : (nb090_alpha_dummy_185 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_185, fv_syn_c0] using (nb090_compact_fv_empty_0134 A)

theorem nb090_wpp_notmem_0463 (h : Var) : (nb090_alpha_dummy_188 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_188, fv_syn_c0] using (nb090_compact_fv_empty_0135 h)

theorem nb090_wpp_notmem_0464 (A : Class) : (nb090_alpha_dummy_183 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_183, fv_syn_c0] using (nb090_compact_fv_empty_0136 A)

theorem nb090_wpp_notmem_0465 (h : Var) : (nb090_alpha_dummy_184 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_184, fv_syn_c0] using (nb090_compact_fv_empty_0137 h)

theorem nb090_wpp_notmem_0466 (A : Class) : (nb090_alpha_dummy_179 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_179, fv_syn_c0] using (nb090_compact_fv_empty_0138 A)

theorem nb090_wpp_notmem_0467 (h : Var) : (nb090_alpha_dummy_181 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_181, fv_syn_c0] using (nb090_compact_fv_empty_0139 h)

theorem nb090_wpp_notmem_0468 (A : Class) : (nb090_alpha_dummy_180 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_180, fv_syn_c0] using (nb090_compact_fv_empty_0140 A)

theorem nb090_wpp_notmem_0469 (h : Var) : (nb090_alpha_dummy_182 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_182, fv_syn_c0] using (nb090_compact_fv_empty_0141 h)

theorem nb090_wpp_notmem_0470 (A : Class) : (nb090_alpha_dummy_172 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_172, fv_syn_c0] using (nb090_compact_fv_empty_0142 A)

theorem nb090_wpp_notmem_0471 (h : Var) : (nb090_alpha_dummy_174 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_174, fv_syn_c0] using (nb090_compact_fv_empty_0143 h)

theorem nb090_wpp_notmem_0472 (A : Class) : (nb090_alpha_dummy_171 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_171, fv_syn_c0] using (nb090_compact_fv_empty_0144 A)

theorem nb090_wpp_notmem_0473 (h : Var) : (nb090_alpha_dummy_173 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_173, fv_syn_c0] using (nb090_compact_fv_empty_0145 h)

theorem nb090_wpp_notmem_0474 (A : Class) : (nb090_alpha_dummy_177 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_177, fv_syn_c0] using (nb090_compact_fv_empty_0146 A)

theorem nb090_wpp_notmem_0475 (h : Var) : (nb090_alpha_dummy_178 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_178, fv_syn_c0] using (nb090_compact_fv_empty_0147 h)

theorem nb090_wpp_notmem_0476 (A : Class) : (nb090_alpha_dummy_175 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_175, fv_syn_c0] using (nb090_compact_fv_empty_0148 A)

theorem nb090_wpp_notmem_0477 (h : Var) : (nb090_alpha_dummy_176 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_176, fv_syn_c0] using (nb090_compact_fv_empty_0149 h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
