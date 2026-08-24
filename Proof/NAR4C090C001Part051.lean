import NAR4C090C001Part050

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

noncomputable def nb090_split_alpha_0028 (v : Var) (u : Var) (A : Class) (h : Var) : TAlphaWff [((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (Wff.classMem (Class.cv (nb090_alpha_dummy_203 A)) (syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))) (Wff.classMem (Class.cv (nb090_alpha_dummy_204 h)) (syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0170 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0171 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0170 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0171 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0200 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0201 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0198 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0199 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_172 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_174 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0174 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0175 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0174 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0175 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0172 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0173 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_187 A), (nb090_alpha_dummy_190 h)), ((nb090_alpha_dummy_186 A), (nb090_alpha_dummy_189 h)), ((nb090_alpha_dummy_185 A), (nb090_alpha_dummy_188 h)), ((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)), ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)), ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)), ((nb090_alpha_dummy_205 A), (nb090_alpha_dummy_206 h)), ((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0097 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0178 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0179 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0176 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0177 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0182 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0183 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0180 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0181 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0178 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0179 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0176 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0177 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0182 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0183 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0180 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0181 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_187 A), (nb090_alpha_dummy_190 h)), ((nb090_alpha_dummy_186 A), (nb090_alpha_dummy_189 h)), ((nb090_alpha_dummy_185 A), (nb090_alpha_dummy_188 h)), ((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)), ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)), ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)), ((nb090_alpha_dummy_205 A), (nb090_alpha_dummy_206 h)), ((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0098 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0186 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0187 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0184 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0185 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0186 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0187 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0184 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0185 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0190 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0191 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0188 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0189 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0190 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0191 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0188 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0189 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0172 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0173 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)), ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)), ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)), ((nb090_alpha_dummy_205 A), (nb090_alpha_dummy_206 h)), ((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0099 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0172 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0173 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0172 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0173 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)), ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)), ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)), ((nb090_alpha_dummy_205 A), (nb090_alpha_dummy_206 h)), ((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0099 v u A h)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0170 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0171 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0170 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0171 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0200 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0201 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0198 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0199 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_172 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_174 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0174 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0175 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0174 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0175 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0172 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0173 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_187 A), (nb090_alpha_dummy_190 h)), ((nb090_alpha_dummy_186 A), (nb090_alpha_dummy_189 h)), ((nb090_alpha_dummy_185 A), (nb090_alpha_dummy_188 h)), ((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)), ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)), ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)), ((nb090_alpha_dummy_205 A), (nb090_alpha_dummy_206 h)), ((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0097 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0178 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0179 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0176 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0177 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0182 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0183 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0180 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0181 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0178 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0179 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0176 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0177 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0182 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0183 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0180 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0181 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_187 A), (nb090_alpha_dummy_190 h)), ((nb090_alpha_dummy_186 A), (nb090_alpha_dummy_189 h)), ((nb090_alpha_dummy_185 A), (nb090_alpha_dummy_188 h)), ((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)), ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)), ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)), ((nb090_alpha_dummy_205 A), (nb090_alpha_dummy_206 h)), ((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0098 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0186 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0187 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0184 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0185 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0186 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0187 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0184 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0185 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0190 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0191 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0188 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0189 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0190 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0191 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0188 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0189 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0172 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0173 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)), ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)), ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)), ((nb090_alpha_dummy_205 A), (nb090_alpha_dummy_206 h)), ((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0099 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0172 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0173 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0172 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0173 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)), ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)), ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)), ((nb090_alpha_dummy_205 A), (nb090_alpha_dummy_206 h)), ((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0099 v u A h))))))))))))))))))))))))

theorem nb090_compact_envfresh_0100 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_203 A) (nb090_alpha_dummy_204 h) (nb090_wpp_notmem_0510 A) (nb090_wpp_notmem_0511 h) (TEnvFresh.consFresh (nb090_alpha_dummy_172 A) (nb090_alpha_dummy_174 h) (nb090_wpp_notmem_0512 A) (nb090_wpp_notmem_0513 h) (TEnvFresh.consFresh (nb090_alpha_dummy_171 A) (nb090_alpha_dummy_173 h) (nb090_wpp_notmem_0514 A) (nb090_wpp_notmem_0515 h) (TEnvFresh.consFresh (nb090_alpha_dummy_201 A) (nb090_alpha_dummy_202 h) (nb090_wpp_notmem_0516 A) (nb090_wpp_notmem_0517 h) (TEnvFresh.consFresh (nb090_alpha_dummy_175 A) (nb090_alpha_dummy_176 h) (nb090_wpp_notmem_0518 A) (nb090_wpp_notmem_0519 h) (TEnvFresh.consFresh (nb090_alpha_dummy_130 A) (nb090_alpha_dummy_132 h) (nb090_wpp_notmem_0432 A) (nb090_wpp_notmem_0433 h) (TEnvFresh.consFresh (nb090_alpha_dummy_129 A) (nb090_alpha_dummy_131 h) (nb090_wpp_notmem_0434 A) (nb090_wpp_notmem_0435 h) (TEnvFresh.consFresh (nb090_alpha_dummy_133 A) (nb090_alpha_dummy_134 h) (nb090_wpp_notmem_0436 A) (nb090_wpp_notmem_0437 h) (TEnvFresh.consFresh (nb090_alpha_dummy_244 A) (nb090_alpha_dummy_246 h) (nb090_wpp_notmem_0720 A) (nb090_wpp_notmem_0721 h) (TEnvFresh.consFresh (nb090_alpha_dummy_243 A) (nb090_alpha_dummy_245 h) (nb090_wpp_notmem_0722 A) (nb090_wpp_notmem_0723 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0240 A) (nb090_wpp_notmem_0241 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0100 A) (nb090_wpp_notmem_0101 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0102 A) (nb090_wpp_notmem_0103 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0104 A) (nb090_wpp_notmem_0105 v u A h) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))))))

noncomputable def nb090_wpp_refl_0100 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0100 v u A h)

theorem nb090_compact_fv_empty_0212 (A : Class) : (nb090_alpha_dummy_307 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0724 (A : Class) : (nb090_alpha_dummy_307 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_307, fv_syn_c1c] using (nb090_compact_fv_empty_0212 A)

theorem nb090_compact_fv_empty_0213 (u : Var) : (nb090_alpha_dummy_310 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0725 (u : Var) : (nb090_alpha_dummy_310 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_310, fv_syn_c1c] using (nb090_compact_fv_empty_0213 u)

theorem nb090_compact_fv_empty_0214 (A : Class) : (nb090_alpha_dummy_306 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0726 (A : Class) : (nb090_alpha_dummy_306 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_306, fv_syn_c1c] using (nb090_compact_fv_empty_0214 A)

theorem nb090_compact_fv_empty_0215 (u : Var) : (nb090_alpha_dummy_309 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0727 (u : Var) : (nb090_alpha_dummy_309 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_309, fv_syn_c1c] using (nb090_compact_fv_empty_0215 u)

theorem nb090_compact_fv_empty_0216 (A : Class) : (nb090_alpha_dummy_305 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0728 (A : Class) : (nb090_alpha_dummy_305 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_305, fv_syn_c1c] using (nb090_compact_fv_empty_0216 A)

theorem nb090_compact_fv_empty_0217 (u : Var) : (nb090_alpha_dummy_308 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0729 (u : Var) : (nb090_alpha_dummy_308 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_308, fv_syn_c1c] using (nb090_compact_fv_empty_0217 u)

theorem nb090_compact_fv_empty_0218 (A : Class) : (nb090_alpha_dummy_303 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0730 (A : Class) : (nb090_alpha_dummy_303 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_303, fv_syn_c1c] using (nb090_compact_fv_empty_0218 A)

theorem nb090_compact_fv_empty_0219 (u : Var) : (nb090_alpha_dummy_304 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0731 (u : Var) : (nb090_alpha_dummy_304 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_304, fv_syn_c1c] using (nb090_compact_fv_empty_0219 u)

theorem nb090_compact_fv_empty_0220 (A : Class) : (nb090_alpha_dummy_299 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0732 (A : Class) : (nb090_alpha_dummy_299 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_299, fv_syn_c1c] using (nb090_compact_fv_empty_0220 A)

theorem nb090_compact_fv_empty_0221 (u : Var) : (nb090_alpha_dummy_301 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0733 (u : Var) : (nb090_alpha_dummy_301 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_301, fv_syn_c1c] using (nb090_compact_fv_empty_0221 u)

theorem nb090_compact_fv_empty_0222 (A : Class) : (nb090_alpha_dummy_300 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0734 (A : Class) : (nb090_alpha_dummy_300 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_300, fv_syn_c1c] using (nb090_compact_fv_empty_0222 A)

theorem nb090_compact_fv_empty_0223 (u : Var) : (nb090_alpha_dummy_302 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0735 (u : Var) : (nb090_alpha_dummy_302 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_302, fv_syn_c1c] using (nb090_compact_fv_empty_0223 u)

theorem nb090_compact_fv_empty_0224 (A : Class) : (nb090_alpha_dummy_292 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0736 (A : Class) : (nb090_alpha_dummy_292 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_292, fv_syn_c1c] using (nb090_compact_fv_empty_0224 A)

theorem nb090_compact_fv_empty_0225 (u : Var) : (nb090_alpha_dummy_294 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0737 (u : Var) : (nb090_alpha_dummy_294 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_294, fv_syn_c1c] using (nb090_compact_fv_empty_0225 u)

theorem nb090_compact_fv_empty_0226 (A : Class) : (nb090_alpha_dummy_291 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0738 (A : Class) : (nb090_alpha_dummy_291 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_291, fv_syn_c1c] using (nb090_compact_fv_empty_0226 A)

theorem nb090_compact_fv_empty_0227 (u : Var) : (nb090_alpha_dummy_293 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0739 (u : Var) : (nb090_alpha_dummy_293 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_293, fv_syn_c1c] using (nb090_compact_fv_empty_0227 u)

theorem nb090_compact_fv_empty_0228 (A : Class) : (nb090_alpha_dummy_297 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0740 (A : Class) : (nb090_alpha_dummy_297 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_297, fv_syn_c1c] using (nb090_compact_fv_empty_0228 A)

theorem nb090_compact_fv_empty_0229 (u : Var) : (nb090_alpha_dummy_298 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0741 (u : Var) : (nb090_alpha_dummy_298 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_298, fv_syn_c1c] using (nb090_compact_fv_empty_0229 u)

theorem nb090_compact_fv_empty_0230 (A : Class) : (nb090_alpha_dummy_295 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0742 (A : Class) : (nb090_alpha_dummy_295 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_295, fv_syn_c1c] using (nb090_compact_fv_empty_0230 A)

theorem nb090_compact_fv_empty_0231 (u : Var) : (nb090_alpha_dummy_296 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0743 (u : Var) : (nb090_alpha_dummy_296 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_296, fv_syn_c1c] using (nb090_compact_fv_empty_0231 u)

theorem nb090_compact_fv_empty_0232 (A : Class) : (nb090_alpha_dummy_283 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0744 (A : Class) : (nb090_alpha_dummy_283 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_283, fv_syn_c1c] using (nb090_compact_fv_empty_0232 A)

theorem nb090_compact_fv_empty_0233 (u : Var) : (nb090_alpha_dummy_284 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0745 (u : Var) : (nb090_alpha_dummy_284 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_284, fv_syn_c1c] using (nb090_compact_fv_empty_0233 u)

theorem nb090_compact_fv_empty_0234 (A : Class) : (nb090_alpha_dummy_285 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0746 (A : Class) : (nb090_alpha_dummy_285 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_285, fv_syn_c1c] using (nb090_compact_fv_empty_0234 A)

theorem nb090_compact_fv_empty_0235 (u : Var) : (nb090_alpha_dummy_286 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0747 (u : Var) : (nb090_alpha_dummy_286 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_286, fv_syn_c1c] using (nb090_compact_fv_empty_0235 u)

theorem nb090_compact_fv_empty_0236 (A : Class) : (nb090_alpha_dummy_288 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0748 (A : Class) : (nb090_alpha_dummy_288 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_288, fv_syn_c1c] using (nb090_compact_fv_empty_0236 A)

theorem nb090_compact_fv_empty_0237 (u : Var) : (nb090_alpha_dummy_290 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0749 (u : Var) : (nb090_alpha_dummy_290 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_290, fv_syn_c1c] using (nb090_compact_fv_empty_0237 u)

theorem nb090_compact_fv_empty_0238 (A : Class) : (nb090_alpha_dummy_287 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0750 (A : Class) : (nb090_alpha_dummy_287 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_287, fv_syn_c1c] using (nb090_compact_fv_empty_0238 A)

theorem nb090_compact_fv_empty_0239 (u : Var) : (nb090_alpha_dummy_289 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0751 (u : Var) : (nb090_alpha_dummy_289 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_289, fv_syn_c1c] using (nb090_compact_fv_empty_0239 u)

theorem nb090_compact_envfresh_0101 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_307 A), (nb090_alpha_dummy_310 u)), ((nb090_alpha_dummy_306 A), (nb090_alpha_dummy_309 u)), ((nb090_alpha_dummy_305 A), (nb090_alpha_dummy_308 u)), ((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_297 A), (nb090_alpha_dummy_298 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_307 A) (nb090_alpha_dummy_310 u) (nb090_wpp_notmem_0724 A) (nb090_wpp_notmem_0725 u) (TEnvFresh.consFresh (nb090_alpha_dummy_306 A) (nb090_alpha_dummy_309 u) (nb090_wpp_notmem_0726 A) (nb090_wpp_notmem_0727 u) (TEnvFresh.consFresh (nb090_alpha_dummy_305 A) (nb090_alpha_dummy_308 u) (nb090_wpp_notmem_0728 A) (nb090_wpp_notmem_0729 u) (TEnvFresh.consFresh (nb090_alpha_dummy_303 A) (nb090_alpha_dummy_304 u) (nb090_wpp_notmem_0730 A) (nb090_wpp_notmem_0731 u) (TEnvFresh.consFresh (nb090_alpha_dummy_299 A) (nb090_alpha_dummy_301 u) (nb090_wpp_notmem_0732 A) (nb090_wpp_notmem_0733 u) (TEnvFresh.consFresh (nb090_alpha_dummy_300 A) (nb090_alpha_dummy_302 u) (nb090_wpp_notmem_0734 A) (nb090_wpp_notmem_0735 u) (TEnvFresh.consFresh (nb090_alpha_dummy_292 A) (nb090_alpha_dummy_294 u) (nb090_wpp_notmem_0736 A) (nb090_wpp_notmem_0737 u) (TEnvFresh.consFresh (nb090_alpha_dummy_291 A) (nb090_alpha_dummy_293 u) (nb090_wpp_notmem_0738 A) (nb090_wpp_notmem_0739 u) (TEnvFresh.consFresh (nb090_alpha_dummy_297 A) (nb090_alpha_dummy_298 u) (nb090_wpp_notmem_0740 A) (nb090_wpp_notmem_0741 u) (TEnvFresh.consFresh (nb090_alpha_dummy_295 A) (nb090_alpha_dummy_296 u) (nb090_wpp_notmem_0742 A) (nb090_wpp_notmem_0743 u) (TEnvFresh.consFresh (nb090_alpha_dummy_283 A) (nb090_alpha_dummy_284 u) (nb090_wpp_notmem_0744 A) (nb090_wpp_notmem_0745 u) (TEnvFresh.consFresh (nb090_alpha_dummy_285 A) (nb090_alpha_dummy_286 u) (nb090_wpp_notmem_0746 A) (nb090_wpp_notmem_0747 u) (TEnvFresh.consFresh (nb090_alpha_dummy_288 A) (nb090_alpha_dummy_290 u) (nb090_wpp_notmem_0748 A) (nb090_wpp_notmem_0749 u) (TEnvFresh.consFresh (nb090_alpha_dummy_287 A) (nb090_alpha_dummy_289 u) (nb090_wpp_notmem_0750 A) (nb090_wpp_notmem_0751 u) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0142 A) (nb090_wpp_notmem_0143 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0020 A) (nb090_wpp_notmem_0021 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0022 A) (nb090_wpp_notmem_0023 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0024 A) (nb090_wpp_notmem_0025 v u A h) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))

noncomputable def nb090_wpp_refl_0101 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_307 A), (nb090_alpha_dummy_310 u)), ((nb090_alpha_dummy_306 A), (nb090_alpha_dummy_309 u)), ((nb090_alpha_dummy_305 A), (nb090_alpha_dummy_308 u)), ((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_297 A), (nb090_alpha_dummy_298 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0101 v u A h)

theorem nb090_wpp_notmem_0752 (A : Class) : (nb090_alpha_dummy_307 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_307, fv_syn_c0] using (nb090_compact_fv_empty_0212 A)

theorem nb090_wpp_notmem_0753 (u : Var) : (nb090_alpha_dummy_310 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_310, fv_syn_c0] using (nb090_compact_fv_empty_0213 u)

theorem nb090_wpp_notmem_0754 (A : Class) : (nb090_alpha_dummy_306 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_306, fv_syn_c0] using (nb090_compact_fv_empty_0214 A)

theorem nb090_wpp_notmem_0755 (u : Var) : (nb090_alpha_dummy_309 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_309, fv_syn_c0] using (nb090_compact_fv_empty_0215 u)

theorem nb090_wpp_notmem_0756 (A : Class) : (nb090_alpha_dummy_305 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_305, fv_syn_c0] using (nb090_compact_fv_empty_0216 A)

theorem nb090_wpp_notmem_0757 (u : Var) : (nb090_alpha_dummy_308 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_308, fv_syn_c0] using (nb090_compact_fv_empty_0217 u)

theorem nb090_wpp_notmem_0758 (A : Class) : (nb090_alpha_dummy_303 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_303, fv_syn_c0] using (nb090_compact_fv_empty_0218 A)

theorem nb090_wpp_notmem_0759 (u : Var) : (nb090_alpha_dummy_304 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_304, fv_syn_c0] using (nb090_compact_fv_empty_0219 u)

theorem nb090_wpp_notmem_0760 (A : Class) : (nb090_alpha_dummy_299 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_299, fv_syn_c0] using (nb090_compact_fv_empty_0220 A)

theorem nb090_wpp_notmem_0761 (u : Var) : (nb090_alpha_dummy_301 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_301, fv_syn_c0] using (nb090_compact_fv_empty_0221 u)

theorem nb090_wpp_notmem_0762 (A : Class) : (nb090_alpha_dummy_300 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_300, fv_syn_c0] using (nb090_compact_fv_empty_0222 A)

theorem nb090_wpp_notmem_0763 (u : Var) : (nb090_alpha_dummy_302 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_302, fv_syn_c0] using (nb090_compact_fv_empty_0223 u)

theorem nb090_wpp_notmem_0764 (A : Class) : (nb090_alpha_dummy_292 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_292, fv_syn_c0] using (nb090_compact_fv_empty_0224 A)

theorem nb090_wpp_notmem_0765 (u : Var) : (nb090_alpha_dummy_294 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_294, fv_syn_c0] using (nb090_compact_fv_empty_0225 u)

theorem nb090_wpp_notmem_0766 (A : Class) : (nb090_alpha_dummy_291 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_291, fv_syn_c0] using (nb090_compact_fv_empty_0226 A)

theorem nb090_wpp_notmem_0767 (u : Var) : (nb090_alpha_dummy_293 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_293, fv_syn_c0] using (nb090_compact_fv_empty_0227 u)

theorem nb090_wpp_notmem_0768 (A : Class) : (nb090_alpha_dummy_297 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_297, fv_syn_c0] using (nb090_compact_fv_empty_0228 A)

theorem nb090_wpp_notmem_0769 (u : Var) : (nb090_alpha_dummy_298 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_298, fv_syn_c0] using (nb090_compact_fv_empty_0229 u)

theorem nb090_wpp_notmem_0770 (A : Class) : (nb090_alpha_dummy_295 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_295, fv_syn_c0] using (nb090_compact_fv_empty_0230 A)

theorem nb090_wpp_notmem_0771 (u : Var) : (nb090_alpha_dummy_296 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_296, fv_syn_c0] using (nb090_compact_fv_empty_0231 u)

theorem nb090_wpp_notmem_0772 (A : Class) : (nb090_alpha_dummy_283 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_283, fv_syn_c0] using (nb090_compact_fv_empty_0232 A)

theorem nb090_wpp_notmem_0773 (u : Var) : (nb090_alpha_dummy_284 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_284, fv_syn_c0] using (nb090_compact_fv_empty_0233 u)

theorem nb090_wpp_notmem_0774 (A : Class) : (nb090_alpha_dummy_285 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_285, fv_syn_c0] using (nb090_compact_fv_empty_0234 A)

theorem nb090_wpp_notmem_0775 (u : Var) : (nb090_alpha_dummy_286 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_286, fv_syn_c0] using (nb090_compact_fv_empty_0235 u)

theorem nb090_wpp_notmem_0776 (A : Class) : (nb090_alpha_dummy_288 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_288, fv_syn_c0] using (nb090_compact_fv_empty_0236 A)

theorem nb090_wpp_notmem_0777 (u : Var) : (nb090_alpha_dummy_290 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_290, fv_syn_c0] using (nb090_compact_fv_empty_0237 u)

theorem nb090_wpp_notmem_0778 (A : Class) : (nb090_alpha_dummy_287 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_287, fv_syn_c0] using (nb090_compact_fv_empty_0238 A)

theorem nb090_wpp_notmem_0779 (u : Var) : (nb090_alpha_dummy_289 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_289, fv_syn_c0] using (nb090_compact_fv_empty_0239 u)

theorem nb090_compact_envfresh_0102 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_307 A), (nb090_alpha_dummy_310 u)), ((nb090_alpha_dummy_306 A), (nb090_alpha_dummy_309 u)), ((nb090_alpha_dummy_305 A), (nb090_alpha_dummy_308 u)), ((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_297 A), (nb090_alpha_dummy_298 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_307 A) (nb090_alpha_dummy_310 u) (nb090_wpp_notmem_0752 A) (nb090_wpp_notmem_0753 u) (TEnvFresh.consFresh (nb090_alpha_dummy_306 A) (nb090_alpha_dummy_309 u) (nb090_wpp_notmem_0754 A) (nb090_wpp_notmem_0755 u) (TEnvFresh.consFresh (nb090_alpha_dummy_305 A) (nb090_alpha_dummy_308 u) (nb090_wpp_notmem_0756 A) (nb090_wpp_notmem_0757 u) (TEnvFresh.consFresh (nb090_alpha_dummy_303 A) (nb090_alpha_dummy_304 u) (nb090_wpp_notmem_0758 A) (nb090_wpp_notmem_0759 u) (TEnvFresh.consFresh (nb090_alpha_dummy_299 A) (nb090_alpha_dummy_301 u) (nb090_wpp_notmem_0760 A) (nb090_wpp_notmem_0761 u) (TEnvFresh.consFresh (nb090_alpha_dummy_300 A) (nb090_alpha_dummy_302 u) (nb090_wpp_notmem_0762 A) (nb090_wpp_notmem_0763 u) (TEnvFresh.consFresh (nb090_alpha_dummy_292 A) (nb090_alpha_dummy_294 u) (nb090_wpp_notmem_0764 A) (nb090_wpp_notmem_0765 u) (TEnvFresh.consFresh (nb090_alpha_dummy_291 A) (nb090_alpha_dummy_293 u) (nb090_wpp_notmem_0766 A) (nb090_wpp_notmem_0767 u) (TEnvFresh.consFresh (nb090_alpha_dummy_297 A) (nb090_alpha_dummy_298 u) (nb090_wpp_notmem_0768 A) (nb090_wpp_notmem_0769 u) (TEnvFresh.consFresh (nb090_alpha_dummy_295 A) (nb090_alpha_dummy_296 u) (nb090_wpp_notmem_0770 A) (nb090_wpp_notmem_0771 u) (TEnvFresh.consFresh (nb090_alpha_dummy_283 A) (nb090_alpha_dummy_284 u) (nb090_wpp_notmem_0772 A) (nb090_wpp_notmem_0773 u) (TEnvFresh.consFresh (nb090_alpha_dummy_285 A) (nb090_alpha_dummy_286 u) (nb090_wpp_notmem_0774 A) (nb090_wpp_notmem_0775 u) (TEnvFresh.consFresh (nb090_alpha_dummy_288 A) (nb090_alpha_dummy_290 u) (nb090_wpp_notmem_0776 A) (nb090_wpp_notmem_0777 u) (TEnvFresh.consFresh (nb090_alpha_dummy_287 A) (nb090_alpha_dummy_289 u) (nb090_wpp_notmem_0778 A) (nb090_wpp_notmem_0779 u) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0174 A) (nb090_wpp_notmem_0175 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0046 A) (nb090_wpp_notmem_0047 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0048 A) (nb090_wpp_notmem_0049 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0050 A) (nb090_wpp_notmem_0051 v u A h) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))

noncomputable def nb090_wpp_refl_0102 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_307 A), (nb090_alpha_dummy_310 u)), ((nb090_alpha_dummy_306 A), (nb090_alpha_dummy_309 u)), ((nb090_alpha_dummy_305 A), (nb090_alpha_dummy_308 u)), ((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_297 A), (nb090_alpha_dummy_298 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0102 v u A h)

theorem nb090_wpp_notmem_0780 (A : Class) : (nb090_alpha_dummy_303 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_303, fv_syn_cnnc] using (nb090_compact_fv_empty_0218 A)

theorem nb090_wpp_notmem_0781 (u : Var) : (nb090_alpha_dummy_304 u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_304, fv_syn_cnnc] using (nb090_compact_fv_empty_0219 u)

theorem nb090_wpp_notmem_0782 (A : Class) : (nb090_alpha_dummy_299 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_299, fv_syn_cnnc] using (nb090_compact_fv_empty_0220 A)

theorem nb090_wpp_notmem_0783 (u : Var) : (nb090_alpha_dummy_301 u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_301, fv_syn_cnnc] using (nb090_compact_fv_empty_0221 u)

theorem nb090_wpp_notmem_0784 (A : Class) : (nb090_alpha_dummy_300 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_300, fv_syn_cnnc] using (nb090_compact_fv_empty_0222 A)

theorem nb090_wpp_notmem_0785 (u : Var) : (nb090_alpha_dummy_302 u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_302, fv_syn_cnnc] using (nb090_compact_fv_empty_0223 u)

theorem nb090_wpp_notmem_0786 (A : Class) : (nb090_alpha_dummy_292 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_292, fv_syn_cnnc] using (nb090_compact_fv_empty_0224 A)

theorem nb090_wpp_notmem_0787 (u : Var) : (nb090_alpha_dummy_294 u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_294, fv_syn_cnnc] using (nb090_compact_fv_empty_0225 u)

theorem nb090_wpp_notmem_0788 (A : Class) : (nb090_alpha_dummy_291 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_291, fv_syn_cnnc] using (nb090_compact_fv_empty_0226 A)

theorem nb090_wpp_notmem_0789 (u : Var) : (nb090_alpha_dummy_293 u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_293, fv_syn_cnnc] using (nb090_compact_fv_empty_0227 u)

theorem nb090_wpp_notmem_0790 (A : Class) : (nb090_alpha_dummy_297 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_297, fv_syn_cnnc] using (nb090_compact_fv_empty_0228 A)

theorem nb090_wpp_notmem_0791 (u : Var) : (nb090_alpha_dummy_298 u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_298, fv_syn_cnnc] using (nb090_compact_fv_empty_0229 u)

theorem nb090_wpp_notmem_0792 (A : Class) : (nb090_alpha_dummy_295 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_295, fv_syn_cnnc] using (nb090_compact_fv_empty_0230 A)

theorem nb090_wpp_notmem_0793 (u : Var) : (nb090_alpha_dummy_296 u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_296, fv_syn_cnnc] using (nb090_compact_fv_empty_0231 u)

theorem nb090_wpp_notmem_0794 (A : Class) : (nb090_alpha_dummy_283 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_283, fv_syn_cnnc] using (nb090_compact_fv_empty_0232 A)

theorem nb090_wpp_notmem_0795 (u : Var) : (nb090_alpha_dummy_284 u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_284, fv_syn_cnnc] using (nb090_compact_fv_empty_0233 u)

theorem nb090_wpp_notmem_0796 (A : Class) : (nb090_alpha_dummy_285 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_285, fv_syn_cnnc] using (nb090_compact_fv_empty_0234 A)

theorem nb090_wpp_notmem_0797 (u : Var) : (nb090_alpha_dummy_286 u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_286, fv_syn_cnnc] using (nb090_compact_fv_empty_0235 u)

theorem nb090_wpp_notmem_0798 (A : Class) : (nb090_alpha_dummy_288 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_288, fv_syn_cnnc] using (nb090_compact_fv_empty_0236 A)

theorem nb090_wpp_notmem_0799 (u : Var) : (nb090_alpha_dummy_290 u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_290, fv_syn_cnnc] using (nb090_compact_fv_empty_0237 u)

theorem nb090_wpp_notmem_0800 (A : Class) : (nb090_alpha_dummy_287 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_287, fv_syn_cnnc] using (nb090_compact_fv_empty_0238 A)

theorem nb090_wpp_notmem_0801 (u : Var) : (nb090_alpha_dummy_289 u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_289, fv_syn_cnnc] using (nb090_compact_fv_empty_0239 u)

theorem nb090_compact_envfresh_0103 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_297 A), (nb090_alpha_dummy_298 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_303 A) (nb090_alpha_dummy_304 u) (nb090_wpp_notmem_0780 A) (nb090_wpp_notmem_0781 u) (TEnvFresh.consFresh (nb090_alpha_dummy_299 A) (nb090_alpha_dummy_301 u) (nb090_wpp_notmem_0782 A) (nb090_wpp_notmem_0783 u) (TEnvFresh.consFresh (nb090_alpha_dummy_300 A) (nb090_alpha_dummy_302 u) (nb090_wpp_notmem_0784 A) (nb090_wpp_notmem_0785 u) (TEnvFresh.consFresh (nb090_alpha_dummy_292 A) (nb090_alpha_dummy_294 u) (nb090_wpp_notmem_0786 A) (nb090_wpp_notmem_0787 u) (TEnvFresh.consFresh (nb090_alpha_dummy_291 A) (nb090_alpha_dummy_293 u) (nb090_wpp_notmem_0788 A) (nb090_wpp_notmem_0789 u) (TEnvFresh.consFresh (nb090_alpha_dummy_297 A) (nb090_alpha_dummy_298 u) (nb090_wpp_notmem_0790 A) (nb090_wpp_notmem_0791 u) (TEnvFresh.consFresh (nb090_alpha_dummy_295 A) (nb090_alpha_dummy_296 u) (nb090_wpp_notmem_0792 A) (nb090_wpp_notmem_0793 u) (TEnvFresh.consFresh (nb090_alpha_dummy_283 A) (nb090_alpha_dummy_284 u) (nb090_wpp_notmem_0794 A) (nb090_wpp_notmem_0795 u) (TEnvFresh.consFresh (nb090_alpha_dummy_285 A) (nb090_alpha_dummy_286 u) (nb090_wpp_notmem_0796 A) (nb090_wpp_notmem_0797 u) (TEnvFresh.consFresh (nb090_alpha_dummy_288 A) (nb090_alpha_dummy_290 u) (nb090_wpp_notmem_0798 A) (nb090_wpp_notmem_0799 u) (TEnvFresh.consFresh (nb090_alpha_dummy_287 A) (nb090_alpha_dummy_289 u) (nb090_wpp_notmem_0800 A) (nb090_wpp_notmem_0801 u) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0200 A) (nb090_wpp_notmem_0201 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0066 A) (nb090_wpp_notmem_0067 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0068 A) (nb090_wpp_notmem_0069 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0070 A) (nb090_wpp_notmem_0071 v u A h) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))

noncomputable def nb090_wpp_refl_0103 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_297 A), (nb090_alpha_dummy_298 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0103 v u A h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
