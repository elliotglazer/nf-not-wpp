import NAR4C077C001Part020

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

noncomputable def nb077_wpp_refl_0035 (x : Var) (F : Class) (I : Class) : TReflOn [((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)), ((nb077_alpha_dummy_191 F I), (nb077_alpha_dummy_193 x)), ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)), ((nb077_alpha_dummy_217 F I), (nb077_alpha_dummy_218 x)), ((nb077_alpha_dummy_215 F I), (nb077_alpha_dummy_216 x)), ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_213 F I), (nb077_alpha_dummy_214 x)), ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0035 x F I)

noncomputable def nb077_split_alpha_0009 (x : Var) (F : Class) (I : Class) : TAlphaWff [((nb077_alpha_dummy_217 F I), (nb077_alpha_dummy_218 x)), ((nb077_alpha_dummy_215 F I), (nb077_alpha_dummy_216 x)), ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_213 F I), (nb077_alpha_dummy_214 x)), ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_217 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))) (Wff.neg (Wff.classMem (Class.cv (nb077_alpha_dummy_217 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))))) (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_218 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))) (Wff.neg (Wff.classMem (Class.cv (nb077_alpha_dummy_218 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0176 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0177 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0176 F I) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0177 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0206 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0207 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0204 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0205 x) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_184 F I))).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_186 x))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0180 F I) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0181 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0180 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0181 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0178 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0179 x) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_199 F I), (nb077_alpha_dummy_202 x)), ((nb077_alpha_dummy_198 F I), (nb077_alpha_dummy_201 x)), ((nb077_alpha_dummy_197 F I), (nb077_alpha_dummy_200 x)), ((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)), ((nb077_alpha_dummy_191 F I), (nb077_alpha_dummy_193 x)), ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)), ((nb077_alpha_dummy_217 F I), (nb077_alpha_dummy_218 x)), ((nb077_alpha_dummy_215 F I), (nb077_alpha_dummy_216 x)), ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_213 F I), (nb077_alpha_dummy_214 x)), ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_c1c) (nb077_wpp_refl_0033 x F I))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0184 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0185 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0182 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0183 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0188 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0189 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0186 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0187 x) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0184 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0185 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0182 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0183 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0188 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0189 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0186 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0187 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_199 F I), (nb077_alpha_dummy_202 x)), ((nb077_alpha_dummy_198 F I), (nb077_alpha_dummy_201 x)), ((nb077_alpha_dummy_197 F I), (nb077_alpha_dummy_200 x)), ((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)), ((nb077_alpha_dummy_191 F I), (nb077_alpha_dummy_193 x)), ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)), ((nb077_alpha_dummy_217 F I), (nb077_alpha_dummy_218 x)), ((nb077_alpha_dummy_215 F I), (nb077_alpha_dummy_216 x)), ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_213 F I), (nb077_alpha_dummy_214 x)), ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_c0) (nb077_wpp_refl_0034 x F I))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0192 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0193 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0190 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0191 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0192 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0193 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0190 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0191 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0196 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0197 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0194 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0195 x) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0196 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0197 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0194 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0195 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0178 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0179 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)), ((nb077_alpha_dummy_191 F I), (nb077_alpha_dummy_193 x)), ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)), ((nb077_alpha_dummy_217 F I), (nb077_alpha_dummy_218 x)), ((nb077_alpha_dummy_215 F I), (nb077_alpha_dummy_216 x)), ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_213 F I), (nb077_alpha_dummy_214 x)), ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_cnnc) (nb077_wpp_refl_0035 x F I))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0178 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0179 x) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0178 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0179 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)), ((nb077_alpha_dummy_191 F I), (nb077_alpha_dummy_193 x)), ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)), ((nb077_alpha_dummy_217 F I), (nb077_alpha_dummy_218 x)), ((nb077_alpha_dummy_215 F I), (nb077_alpha_dummy_216 x)), ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_213 F I), (nb077_alpha_dummy_214 x)), ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_cnnc) (nb077_wpp_refl_0035 x F I)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0176 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0177 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0176 F I) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0177 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0206 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0207 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0204 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0205 x) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_184 F I))).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_186 x))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0180 F I) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0181 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0180 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0181 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0178 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0179 x) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_199 F I), (nb077_alpha_dummy_202 x)), ((nb077_alpha_dummy_198 F I), (nb077_alpha_dummy_201 x)), ((nb077_alpha_dummy_197 F I), (nb077_alpha_dummy_200 x)), ((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)), ((nb077_alpha_dummy_191 F I), (nb077_alpha_dummy_193 x)), ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)), ((nb077_alpha_dummy_217 F I), (nb077_alpha_dummy_218 x)), ((nb077_alpha_dummy_215 F I), (nb077_alpha_dummy_216 x)), ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_213 F I), (nb077_alpha_dummy_214 x)), ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_c1c) (nb077_wpp_refl_0033 x F I))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0184 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0185 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0182 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0183 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0188 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0189 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0186 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0187 x) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0184 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0185 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0182 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0183 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0188 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0189 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0186 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0187 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_199 F I), (nb077_alpha_dummy_202 x)), ((nb077_alpha_dummy_198 F I), (nb077_alpha_dummy_201 x)), ((nb077_alpha_dummy_197 F I), (nb077_alpha_dummy_200 x)), ((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)), ((nb077_alpha_dummy_191 F I), (nb077_alpha_dummy_193 x)), ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)), ((nb077_alpha_dummy_217 F I), (nb077_alpha_dummy_218 x)), ((nb077_alpha_dummy_215 F I), (nb077_alpha_dummy_216 x)), ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_213 F I), (nb077_alpha_dummy_214 x)), ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_c0) (nb077_wpp_refl_0034 x F I))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0192 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0193 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0190 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0191 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0192 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0193 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0190 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0191 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0196 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0197 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0194 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0195 x) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0196 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0197 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0194 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0195 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0178 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0179 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)), ((nb077_alpha_dummy_191 F I), (nb077_alpha_dummy_193 x)), ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)), ((nb077_alpha_dummy_217 F I), (nb077_alpha_dummy_218 x)), ((nb077_alpha_dummy_215 F I), (nb077_alpha_dummy_216 x)), ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_213 F I), (nb077_alpha_dummy_214 x)), ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_cnnc) (nb077_wpp_refl_0035 x F I))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0178 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0179 x) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0178 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0179 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)), ((nb077_alpha_dummy_191 F I), (nb077_alpha_dummy_193 x)), ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)), ((nb077_alpha_dummy_217 F I), (nb077_alpha_dummy_218 x)), ((nb077_alpha_dummy_215 F I), (nb077_alpha_dummy_216 x)), ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_213 F I), (nb077_alpha_dummy_214 x)), ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_cnnc) (nb077_wpp_refl_0035 x F I))))))))))))))))))))

theorem nb077_wpp_notmem_0544 (F : Class) (I : Class) : (nb077_alpha_dummy_215 F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_215, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0164 F I)

theorem nb077_wpp_notmem_0545 (x : Var) : (nb077_alpha_dummy_216 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_216, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0165 x)

theorem nb077_wpp_notmem_0546 (F : Class) (I : Class) : (nb077_alpha_dummy_184 F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_184, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0152 F I)

theorem nb077_wpp_notmem_0547 (x : Var) : (nb077_alpha_dummy_186 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_186, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0153 x)

theorem nb077_wpp_notmem_0548 (F : Class) (I : Class) : (nb077_alpha_dummy_183 F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_183, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0154 F I)

theorem nb077_wpp_notmem_0549 (x : Var) : (nb077_alpha_dummy_185 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_185, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0155 x)

theorem nb077_wpp_notmem_0550 (F : Class) (I : Class) : (nb077_alpha_dummy_213 F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_213, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0166 F I)

theorem nb077_wpp_notmem_0551 (x : Var) : (nb077_alpha_dummy_214 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_214, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0167 x)

theorem nb077_wpp_notmem_0552 (F : Class) (I : Class) : (nb077_alpha_dummy_187 F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_187, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0158 F I)

theorem nb077_wpp_notmem_0553 (x : Var) : (nb077_alpha_dummy_188 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_188, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0159 x)

theorem nb077_wpp_notmem_0554 (F : Class) (I : Class) : (nb077_alpha_dummy_141 F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_141, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0160 F I)

theorem nb077_wpp_notmem_0555 (x : Var) : (nb077_alpha_dummy_144 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_144, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0161 x)

theorem nb077_compact_envfresh_0036 (x : Var) (F : Class) (I : Class) : TEnvFresh [((nb077_alpha_dummy_215 F I), (nb077_alpha_dummy_216 x)), ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_213 F I), (nb077_alpha_dummy_214 x)), ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb077_alpha_dummy_215 F I) (nb077_alpha_dummy_216 x) (nb077_wpp_notmem_0544 F I) (nb077_wpp_notmem_0545 x) (TEnvFresh.consFresh (nb077_alpha_dummy_184 F I) (nb077_alpha_dummy_186 x) (nb077_wpp_notmem_0546 F I) (nb077_wpp_notmem_0547 x) (TEnvFresh.consFresh (nb077_alpha_dummy_183 F I) (nb077_alpha_dummy_185 x) (nb077_wpp_notmem_0548 F I) (nb077_wpp_notmem_0549 x) (TEnvFresh.consFresh (nb077_alpha_dummy_213 F I) (nb077_alpha_dummy_214 x) (nb077_wpp_notmem_0550 F I) (nb077_wpp_notmem_0551 x) (TEnvFresh.consFresh (nb077_alpha_dummy_187 F I) (nb077_alpha_dummy_188 x) (nb077_wpp_notmem_0552 F I) (nb077_wpp_notmem_0553 x) (TEnvFresh.consFresh (nb077_alpha_dummy_141 F I) (nb077_alpha_dummy_144 x) (nb077_wpp_notmem_0554 F I) (nb077_wpp_notmem_0555 x) (TEnvFresh.consFresh (nb077_alpha_dummy_140 F I) (nb077_alpha_dummy_143 x) (nb077_wpp_notmem_0460 F I) (nb077_wpp_notmem_0461 x) (TEnvFresh.consFresh (nb077_alpha_dummy_139 F I) (nb077_alpha_dummy_142 x) (nb077_wpp_notmem_0462 F I) (nb077_wpp_notmem_0463 x) (TEnvFresh.consFresh (nb077_alpha_dummy_145 F I) (nb077_alpha_dummy_146 x) (nb077_wpp_notmem_0464 F I) (nb077_wpp_notmem_0465 x) (TEnvFresh.consFresh (nb077_alpha_dummy_061 F I) (nb077_alpha_dummy_064 x) (nb077_wpp_notmem_0358 F I) (nb077_wpp_notmem_0359 x) (TEnvFresh.consFresh (nb077_alpha_dummy_060 F I) (nb077_alpha_dummy_063 x) (nb077_wpp_notmem_0260 F I) (nb077_wpp_notmem_0261 x) (TEnvFresh.consFresh (nb077_alpha_dummy_059 F I) (nb077_alpha_dummy_062 x) (nb077_wpp_notmem_0262 F I) (nb077_wpp_notmem_0263 x) (TEnvFresh.consFresh (nb077_alpha_dummy_065 F I) (nb077_alpha_dummy_066 x) (nb077_wpp_notmem_0264 F I) (nb077_wpp_notmem_0265 x) (TEnvFresh.consFresh (nb077_alpha_dummy_057 F I) (nb077_alpha_dummy_058 x F) (nb077_wpp_notmem_0266 F I) (nb077_wpp_notmem_0267 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_055 F I) (nb077_alpha_dummy_056 x F) (nb077_wpp_notmem_0268 F I) (nb077_wpp_notmem_0269 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_016 F I) (nb077_alpha_dummy_018 x F I) (nb077_wpp_notmem_0134 F I) (nb077_wpp_notmem_0135 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_015 F I) (nb077_alpha_dummy_017 x F I) (nb077_wpp_notmem_0136 F I) (nb077_wpp_notmem_0137 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_013 F I) (nb077_alpha_dummy_014 x F I) (nb077_wpp_notmem_0138 F I) (nb077_wpp_notmem_0139 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_011 F I) (nb077_alpha_dummy_012 x F I) (nb077_wpp_notmem_0140 F I) (nb077_wpp_notmem_0141 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I) (nb077_alpha_dummy_002 x F I) (nb077_wpp_notmem_0142 F I) (nb077_wpp_notmem_0143 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I) (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0144 F I) (nb077_wpp_notmem_0145 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I) (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0146 F I) (nb077_wpp_notmem_0147 x F I) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))))))))))))))

noncomputable def nb077_wpp_refl_0036 (x : Var) (F : Class) (I : Class) : TReflOn [((nb077_alpha_dummy_215 F I), (nb077_alpha_dummy_216 x)), ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_213 F I), (nb077_alpha_dummy_214 x)), ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0036 x F I)

theorem nb077_wpp_notmem_0556 (F : Class) (I : Class) : (nb077_alpha_dummy_141 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_141, fv_syn_c1st] using (nb077_compact_fv_empty_0160 F I)

theorem nb077_wpp_notmem_0557 (x : Var) : (nb077_alpha_dummy_144 x) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_144, fv_syn_c1st] using (nb077_compact_fv_empty_0161 x)

theorem nb077_wpp_notmem_0558 (F : Class) (I : Class) : (nb077_alpha_dummy_140 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_140, fv_syn_c1st] using (nb077_compact_fv_empty_0128 F I)

theorem nb077_wpp_notmem_0559 (x : Var) : (nb077_alpha_dummy_143 x) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_143, fv_syn_c1st] using (nb077_compact_fv_empty_0129 x)

theorem nb077_wpp_notmem_0560 (F : Class) (I : Class) : (nb077_alpha_dummy_139 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_139, fv_syn_c1st] using (nb077_compact_fv_empty_0130 F I)

theorem nb077_wpp_notmem_0561 (x : Var) : (nb077_alpha_dummy_142 x) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_142, fv_syn_c1st] using (nb077_compact_fv_empty_0131 x)

theorem nb077_wpp_notmem_0562 (F : Class) (I : Class) : (nb077_alpha_dummy_145 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_145, fv_syn_c1st] using (nb077_compact_fv_empty_0132 F I)

theorem nb077_wpp_notmem_0563 (x : Var) : (nb077_alpha_dummy_146 x) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_146, fv_syn_c1st] using (nb077_compact_fv_empty_0133 x)

theorem nb077_wpp_notmem_0564 (F : Class) (I : Class) : (nb077_alpha_dummy_061 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_061, fv_syn_c1st] using (nb077_compact_fv_empty_0100 F I)

theorem nb077_wpp_notmem_0565 (x : Var) : (nb077_alpha_dummy_064 x) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_064, fv_syn_c1st] using (nb077_compact_fv_empty_0101 x)

theorem nb077_wpp_notmem_0566 (F : Class) (I : Class) : (nb077_alpha_dummy_060 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_060, fv_syn_c1st] using (nb077_compact_fv_empty_0064 F I)

theorem nb077_wpp_notmem_0567 (x : Var) : (nb077_alpha_dummy_063 x) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_063, fv_syn_c1st] using (nb077_compact_fv_empty_0065 x)

theorem nb077_wpp_notmem_0568 (F : Class) (I : Class) : (nb077_alpha_dummy_059 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_059, fv_syn_c1st] using (nb077_compact_fv_empty_0066 F I)

theorem nb077_wpp_notmem_0569 (x : Var) : (nb077_alpha_dummy_062 x) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_062, fv_syn_c1st] using (nb077_compact_fv_empty_0067 x)

theorem nb077_wpp_notmem_0570 (F : Class) (I : Class) : (nb077_alpha_dummy_065 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_065, fv_syn_c1st] using (nb077_compact_fv_empty_0068 F I)

theorem nb077_wpp_notmem_0571 (x : Var) : (nb077_alpha_dummy_066 x) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_066, fv_syn_c1st] using (nb077_compact_fv_empty_0069 x)

theorem nb077_wpp_notmem_0572 (F : Class) (I : Class) : (nb077_alpha_dummy_057 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_057, fv_syn_c1st] using (nb077_compact_fv_empty_0070 F I)

theorem nb077_wpp_notmem_0573 (x : Var) (F : Class) : (nb077_alpha_dummy_058 x F) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_058, fv_syn_c1st] using (nb077_compact_fv_empty_0071 x F)

theorem nb077_wpp_notmem_0574 (F : Class) (I : Class) : (nb077_alpha_dummy_055 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_055, fv_syn_c1st] using (nb077_compact_fv_empty_0072 F I)

theorem nb077_wpp_notmem_0575 (x : Var) (F : Class) : (nb077_alpha_dummy_056 x F) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_056, fv_syn_c1st] using (nb077_compact_fv_empty_0073 x F)

theorem nb077_wpp_notmem_0576 (F : Class) (I : Class) : (nb077_alpha_dummy_016 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_016, fv_syn_c1st] using (nb077_compact_fv_empty_0030 F I)

theorem nb077_wpp_notmem_0577 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_018 x F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_018, fv_syn_c1st] using (nb077_compact_fv_empty_0031 x F I)

theorem nb077_wpp_notmem_0578 (F : Class) (I : Class) : (nb077_alpha_dummy_015 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_015, fv_syn_c1st] using (nb077_compact_fv_empty_0032 F I)

theorem nb077_wpp_notmem_0579 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_017 x F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_017, fv_syn_c1st] using (nb077_compact_fv_empty_0033 x F I)

theorem nb077_wpp_notmem_0580 (F : Class) (I : Class) : (nb077_alpha_dummy_013 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_013, fv_syn_c1st] using (nb077_compact_fv_empty_0034 F I)

theorem nb077_wpp_notmem_0581 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_014 x F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_014, fv_syn_c1st] using (nb077_compact_fv_empty_0035 x F I)

theorem nb077_wpp_notmem_0582 (F : Class) (I : Class) : (nb077_alpha_dummy_011 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_011, fv_syn_c1st] using (nb077_compact_fv_empty_0036 F I)

theorem nb077_wpp_notmem_0583 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_012 x F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_012, fv_syn_c1st] using (nb077_compact_fv_empty_0037 x F I)

theorem nb077_wpp_notmem_0584 (F : Class) (I : Class) : (nb077_alpha_dummy_001 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_001, fv_syn_c1st] using (nb077_compact_fv_empty_0004 F I)

theorem nb077_wpp_notmem_0585 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_002 x F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_002, fv_syn_c1st] using (nb077_compact_fv_empty_0005 x F I)

theorem nb077_wpp_notmem_0586 (F : Class) (I : Class) : (nb077_alpha_dummy_004 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_004, fv_syn_c1st] using (nb077_compact_fv_empty_0006 F I)

theorem nb077_wpp_notmem_0587 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_006 x F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_006, fv_syn_c1st] using (nb077_compact_fv_empty_0007 x F I)

theorem nb077_wpp_notmem_0588 (F : Class) (I : Class) : (nb077_alpha_dummy_003 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_003, fv_syn_c1st] using (nb077_compact_fv_empty_0008 F I)

theorem nb077_wpp_notmem_0589 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_005 x F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_005, fv_syn_c1st] using (nb077_compact_fv_empty_0009 x F I)

theorem nb077_compact_envfresh_0037 (x : Var) (F : Class) (I : Class) : TEnvFresh [((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_c1st)).fv := by
  exact (TEnvFresh.consFresh (nb077_alpha_dummy_141 F I) (nb077_alpha_dummy_144 x) (nb077_wpp_notmem_0556 F I) (nb077_wpp_notmem_0557 x) (TEnvFresh.consFresh (nb077_alpha_dummy_140 F I) (nb077_alpha_dummy_143 x) (nb077_wpp_notmem_0558 F I) (nb077_wpp_notmem_0559 x) (TEnvFresh.consFresh (nb077_alpha_dummy_139 F I) (nb077_alpha_dummy_142 x) (nb077_wpp_notmem_0560 F I) (nb077_wpp_notmem_0561 x) (TEnvFresh.consFresh (nb077_alpha_dummy_145 F I) (nb077_alpha_dummy_146 x) (nb077_wpp_notmem_0562 F I) (nb077_wpp_notmem_0563 x) (TEnvFresh.consFresh (nb077_alpha_dummy_061 F I) (nb077_alpha_dummy_064 x) (nb077_wpp_notmem_0564 F I) (nb077_wpp_notmem_0565 x) (TEnvFresh.consFresh (nb077_alpha_dummy_060 F I) (nb077_alpha_dummy_063 x) (nb077_wpp_notmem_0566 F I) (nb077_wpp_notmem_0567 x) (TEnvFresh.consFresh (nb077_alpha_dummy_059 F I) (nb077_alpha_dummy_062 x) (nb077_wpp_notmem_0568 F I) (nb077_wpp_notmem_0569 x) (TEnvFresh.consFresh (nb077_alpha_dummy_065 F I) (nb077_alpha_dummy_066 x) (nb077_wpp_notmem_0570 F I) (nb077_wpp_notmem_0571 x) (TEnvFresh.consFresh (nb077_alpha_dummy_057 F I) (nb077_alpha_dummy_058 x F) (nb077_wpp_notmem_0572 F I) (nb077_wpp_notmem_0573 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_055 F I) (nb077_alpha_dummy_056 x F) (nb077_wpp_notmem_0574 F I) (nb077_wpp_notmem_0575 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_016 F I) (nb077_alpha_dummy_018 x F I) (nb077_wpp_notmem_0576 F I) (nb077_wpp_notmem_0577 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_015 F I) (nb077_alpha_dummy_017 x F I) (nb077_wpp_notmem_0578 F I) (nb077_wpp_notmem_0579 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_013 F I) (nb077_alpha_dummy_014 x F I) (nb077_wpp_notmem_0580 F I) (nb077_wpp_notmem_0581 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_011 F I) (nb077_alpha_dummy_012 x F I) (nb077_wpp_notmem_0582 F I) (nb077_wpp_notmem_0583 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I) (nb077_alpha_dummy_002 x F I) (nb077_wpp_notmem_0584 F I) (nb077_wpp_notmem_0585 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I) (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0586 F I) (nb077_wpp_notmem_0587 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I) (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0588 F I) (nb077_wpp_notmem_0589 x F I) (TEnvFresh.nil ((syn_c1st)).fv))))))))))))))))))

noncomputable def nb077_wpp_refl_0037 (x : Var) (F : Class) (I : Class) : TReflOn [((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_c1st)).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0037 x F I)

theorem nb077_compact_fv_empty_0168 (F : Class) (I : Class) : (nb077_alpha_dummy_235 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0590 (F : Class) (I : Class) : (nb077_alpha_dummy_235 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_235, fv_syn_c1c] using (nb077_compact_fv_empty_0168 F I)

theorem nb077_compact_fv_empty_0169 (x : Var) : (nb077_alpha_dummy_238 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0591 (x : Var) : (nb077_alpha_dummy_238 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_238, fv_syn_c1c] using (nb077_compact_fv_empty_0169 x)

theorem nb077_compact_fv_empty_0170 (F : Class) (I : Class) : (nb077_alpha_dummy_234 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0592 (F : Class) (I : Class) : (nb077_alpha_dummy_234 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_234, fv_syn_c1c] using (nb077_compact_fv_empty_0170 F I)

theorem nb077_compact_fv_empty_0171 (x : Var) : (nb077_alpha_dummy_237 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0593 (x : Var) : (nb077_alpha_dummy_237 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_237, fv_syn_c1c] using (nb077_compact_fv_empty_0171 x)

theorem nb077_compact_fv_empty_0172 (F : Class) (I : Class) : (nb077_alpha_dummy_233 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0594 (F : Class) (I : Class) : (nb077_alpha_dummy_233 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_233, fv_syn_c1c] using (nb077_compact_fv_empty_0172 F I)

theorem nb077_compact_fv_empty_0173 (x : Var) : (nb077_alpha_dummy_236 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0595 (x : Var) : (nb077_alpha_dummy_236 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_236, fv_syn_c1c] using (nb077_compact_fv_empty_0173 x)

theorem nb077_compact_fv_empty_0174 (F : Class) (I : Class) : (nb077_alpha_dummy_231 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0596 (F : Class) (I : Class) : (nb077_alpha_dummy_231 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_231, fv_syn_c1c] using (nb077_compact_fv_empty_0174 F I)

theorem nb077_compact_fv_empty_0175 (x : Var) : (nb077_alpha_dummy_232 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0597 (x : Var) : (nb077_alpha_dummy_232 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_232, fv_syn_c1c] using (nb077_compact_fv_empty_0175 x)

theorem nb077_compact_fv_empty_0176 (F : Class) (I : Class) : (nb077_alpha_dummy_227 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0598 (F : Class) (I : Class) : (nb077_alpha_dummy_227 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_227, fv_syn_c1c] using (nb077_compact_fv_empty_0176 F I)

theorem nb077_compact_fv_empty_0177 (x : Var) : (nb077_alpha_dummy_229 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0599 (x : Var) : (nb077_alpha_dummy_229 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_229, fv_syn_c1c] using (nb077_compact_fv_empty_0177 x)

theorem nb077_compact_fv_empty_0178 (F : Class) (I : Class) : (nb077_alpha_dummy_228 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0600 (F : Class) (I : Class) : (nb077_alpha_dummy_228 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_228, fv_syn_c1c] using (nb077_compact_fv_empty_0178 F I)

theorem nb077_compact_fv_empty_0179 (x : Var) : (nb077_alpha_dummy_230 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0601 (x : Var) : (nb077_alpha_dummy_230 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_230, fv_syn_c1c] using (nb077_compact_fv_empty_0179 x)

theorem nb077_compact_fv_empty_0180 (F : Class) (I : Class) : (nb077_alpha_dummy_220 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0602 (F : Class) (I : Class) : (nb077_alpha_dummy_220 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_220, fv_syn_c1c] using (nb077_compact_fv_empty_0180 F I)

theorem nb077_compact_fv_empty_0181 (x : Var) : (nb077_alpha_dummy_222 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0603 (x : Var) : (nb077_alpha_dummy_222 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_222, fv_syn_c1c] using (nb077_compact_fv_empty_0181 x)

theorem nb077_compact_fv_empty_0182 (F : Class) (I : Class) : (nb077_alpha_dummy_219 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0604 (F : Class) (I : Class) : (nb077_alpha_dummy_219 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_219, fv_syn_c1c] using (nb077_compact_fv_empty_0182 F I)

theorem nb077_compact_fv_empty_0183 (x : Var) : (nb077_alpha_dummy_221 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0605 (x : Var) : (nb077_alpha_dummy_221 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_221, fv_syn_c1c] using (nb077_compact_fv_empty_0183 x)

theorem nb077_compact_fv_empty_0184 (F : Class) (I : Class) : (nb077_alpha_dummy_225 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0606 (F : Class) (I : Class) : (nb077_alpha_dummy_225 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_225, fv_syn_c1c] using (nb077_compact_fv_empty_0184 F I)

theorem nb077_compact_fv_empty_0185 (x : Var) : (nb077_alpha_dummy_226 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0607 (x : Var) : (nb077_alpha_dummy_226 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_226, fv_syn_c1c] using (nb077_compact_fv_empty_0185 x)

theorem nb077_compact_fv_empty_0186 (F : Class) (I : Class) : (nb077_alpha_dummy_223 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0608 (F : Class) (I : Class) : (nb077_alpha_dummy_223 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_223, fv_syn_c1c] using (nb077_compact_fv_empty_0186 F I)

theorem nb077_compact_fv_empty_0187 (x : Var) : (nb077_alpha_dummy_224 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0609 (x : Var) : (nb077_alpha_dummy_224 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_224, fv_syn_c1c] using (nb077_compact_fv_empty_0187 x)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
