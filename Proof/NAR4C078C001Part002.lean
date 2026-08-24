import NAR4C078C001Part001

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

noncomputable def nb078_alpha_dummy_150 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_151 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_146)) (Class.cv (nb078_alpha_dummy_147)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_146)) (Class.cv (nb078_alpha_dummy_147)))).fv) 0)

noncomputable def nb078_alpha_dummy_152 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_149 f)) (Class.cv (nb078_alpha_dummy_150 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_149 f)) (Class.cv (nb078_alpha_dummy_150 f)))).fv) 0)

noncomputable def nb078_alpha_dummy_153 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_146))).fv ∪ ((Class.cv (nb078_alpha_dummy_147))).fv) 0)

noncomputable def nb078_alpha_dummy_154 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_150 f))).fv) 0)

noncomputable def nb078_alpha_dummy_155 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_146)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_147)))).fv) 0)

noncomputable def nb078_alpha_dummy_156 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_149 f)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_150 f)))).fv) 0)

noncomputable def nb078_alpha_dummy_157 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_146))).fv ∪ ((Class.cv (nb078_alpha_dummy_146))).fv) 0)

noncomputable def nb078_alpha_dummy_158 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_149 f))).fv) 0)

noncomputable def nb078_alpha_dummy_159 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_147))).fv ∪ ((Class.cv (nb078_alpha_dummy_147))).fv) 0)

noncomputable def nb078_alpha_dummy_160 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_150 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_150 f))).fv) 0)

noncomputable def nb078_alpha_dummy_161 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_131) (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_089)) (Wff.classEq (Class.cv (nb078_alpha_dummy_131)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_132))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_131) (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_089)) (Wff.classEq (Class.cv (nb078_alpha_dummy_131)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_132))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_162 (f : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_133 f) (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_091 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_133 f) (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_091 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_163 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_132))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_164 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_165 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_132)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_132)))).fv) 0)

noncomputable def nb078_alpha_dummy_166 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))).fv) 0)

noncomputable def nb078_alpha_dummy_167 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_011))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) 0)

noncomputable def nb078_alpha_dummy_168 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_011))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) 1)

noncomputable def nb078_alpha_dummy_169 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) 0)

noncomputable def nb078_alpha_dummy_170 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) 1)

noncomputable def nb078_alpha_dummy_171 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_167) (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_011)) (Wff.classEq (Class.cv (nb078_alpha_dummy_167)) (syn_cphi (Class.cv (nb078_alpha_dummy_168)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_167) (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_010)) (Wff.classEq (Class.cv (nb078_alpha_dummy_167)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_168))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_172 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_169 f) (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_014 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_169 f) (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_013 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_173 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_167) (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_011)) (Wff.classEq (Class.cv (nb078_alpha_dummy_167)) (syn_cphi (Class.cv (nb078_alpha_dummy_168))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_167) (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_011)) (Wff.classEq (Class.cv (nb078_alpha_dummy_167)) (syn_cphi (Class.cv (nb078_alpha_dummy_168))))))).fv) 0)

noncomputable def nb078_alpha_dummy_174 (f : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_169 f) (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_014 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_169 f) (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_014 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))))))).fv) 0)

noncomputable def nb078_alpha_dummy_175 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_168))).fv) 0)

noncomputable def nb078_alpha_dummy_176 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_168))).fv) 1)

noncomputable def nb078_alpha_dummy_177 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_170 f))).fv) 0)

noncomputable def nb078_alpha_dummy_178 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_170 f))).fv) 1)

noncomputable def nb078_alpha_dummy_179 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_175)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_175)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_175))).fv) 0)

noncomputable def nb078_alpha_dummy_180 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_177 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_177 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_177 f))).fv) 0)

noncomputable def nb078_alpha_dummy_181 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_182 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_183 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_184 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_185 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_186 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_187 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_182)) (Class.cv (nb078_alpha_dummy_183)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_182)) (Class.cv (nb078_alpha_dummy_183)))).fv) 0)

noncomputable def nb078_alpha_dummy_188 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_185 f)) (Class.cv (nb078_alpha_dummy_186 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_185 f)) (Class.cv (nb078_alpha_dummy_186 f)))).fv) 0)

noncomputable def nb078_alpha_dummy_189 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_182))).fv ∪ ((Class.cv (nb078_alpha_dummy_183))).fv) 0)

noncomputable def nb078_alpha_dummy_190 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_186 f))).fv) 0)

noncomputable def nb078_alpha_dummy_191 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_182)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_183)))).fv) 0)

noncomputable def nb078_alpha_dummy_192 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_185 f)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_186 f)))).fv) 0)

noncomputable def nb078_alpha_dummy_193 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_182))).fv ∪ ((Class.cv (nb078_alpha_dummy_182))).fv) 0)

noncomputable def nb078_alpha_dummy_194 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_185 f))).fv) 0)

noncomputable def nb078_alpha_dummy_195 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_183))).fv ∪ ((Class.cv (nb078_alpha_dummy_183))).fv) 0)

noncomputable def nb078_alpha_dummy_196 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_186 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_186 f))).fv) 0)

noncomputable def nb078_alpha_dummy_197 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_167) (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_010)) (Wff.classEq (Class.cv (nb078_alpha_dummy_167)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_168))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_167) (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_010)) (Wff.classEq (Class.cv (nb078_alpha_dummy_167)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_168))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_198 (f : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_169 f) (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_013 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_169 f) (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_013 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_199 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_168))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_200 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_201 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_168)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_168)))).fv) 0)

noncomputable def nb078_alpha_dummy_202 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))).fv) 0)

noncomputable def nb078_alpha_dummy_203 : Var := (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb078_alpha_dummy_204 : Var := (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb078_alpha_dummy_205 (f : Var) : Var := (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb078_alpha_dummy_206 (f : Var) : Var := (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb078_alpha_dummy_207 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_204))).fv ∪ ((Class.cv (nb078_alpha_dummy_203))).fv) 0)

noncomputable def nb078_alpha_dummy_208 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_204))).fv ∪ ((Class.cv (nb078_alpha_dummy_203))).fv) 1)

noncomputable def nb078_alpha_dummy_209 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_206 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_205 f))).fv) 0)

noncomputable def nb078_alpha_dummy_210 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_206 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_205 f))).fv) 1)

noncomputable def nb078_alpha_dummy_211 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_207) (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_204)) (Wff.classEq (Class.cv (nb078_alpha_dummy_207)) (syn_cphi (Class.cv (nb078_alpha_dummy_208)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_207) (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_203)) (Wff.classEq (Class.cv (nb078_alpha_dummy_207)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_208))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_212 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_209 f) (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_206 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_209 f) (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_205 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_213 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_207) (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_204)) (Wff.classEq (Class.cv (nb078_alpha_dummy_207)) (syn_cphi (Class.cv (nb078_alpha_dummy_208))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_207) (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_204)) (Wff.classEq (Class.cv (nb078_alpha_dummy_207)) (syn_cphi (Class.cv (nb078_alpha_dummy_208))))))).fv) 0)

noncomputable def nb078_alpha_dummy_214 (f : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_209 f) (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_206 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_209 f) (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_206 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))))))).fv) 0)

noncomputable def nb078_alpha_dummy_215 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_208))).fv) 0)

noncomputable def nb078_alpha_dummy_216 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_208))).fv) 1)

noncomputable def nb078_alpha_dummy_217 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_210 f))).fv) 0)

noncomputable def nb078_alpha_dummy_218 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_210 f))).fv) 1)

noncomputable def nb078_alpha_dummy_219 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_215)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_215)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_215))).fv) 0)

noncomputable def nb078_alpha_dummy_220 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_217 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_217 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_217 f))).fv) 0)

noncomputable def nb078_alpha_dummy_221 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_222 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_223 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_224 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_225 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_226 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_227 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_222)) (Class.cv (nb078_alpha_dummy_223)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_222)) (Class.cv (nb078_alpha_dummy_223)))).fv) 0)

noncomputable def nb078_alpha_dummy_228 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_225 f)) (Class.cv (nb078_alpha_dummy_226 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_225 f)) (Class.cv (nb078_alpha_dummy_226 f)))).fv) 0)

noncomputable def nb078_alpha_dummy_229 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_222))).fv ∪ ((Class.cv (nb078_alpha_dummy_223))).fv) 0)

noncomputable def nb078_alpha_dummy_230 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_225 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_226 f))).fv) 0)

noncomputable def nb078_alpha_dummy_231 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_222)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_223)))).fv) 0)

noncomputable def nb078_alpha_dummy_232 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_225 f)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_226 f)))).fv) 0)

noncomputable def nb078_alpha_dummy_233 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_222))).fv ∪ ((Class.cv (nb078_alpha_dummy_222))).fv) 0)

noncomputable def nb078_alpha_dummy_234 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_225 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_225 f))).fv) 0)

noncomputable def nb078_alpha_dummy_235 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_223))).fv ∪ ((Class.cv (nb078_alpha_dummy_223))).fv) 0)

noncomputable def nb078_alpha_dummy_236 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_226 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_226 f))).fv) 0)

noncomputable def nb078_alpha_dummy_237 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_207) (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_203)) (Wff.classEq (Class.cv (nb078_alpha_dummy_207)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_208))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_207) (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_203)) (Wff.classEq (Class.cv (nb078_alpha_dummy_207)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_208))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_238 (f : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_209 f) (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_205 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_209 f) (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_205 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_239 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_208))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_240 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_241 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_208)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_208)))).fv) 0)

noncomputable def nb078_alpha_dummy_242 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))).fv) 0)

noncomputable def nb078_alpha_dummy_243 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb078_alpha_dummy_244 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb078_alpha_dummy_245 (f : Var) : Var := (freshVar (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb078_alpha_dummy_246 (f : Var) : Var := (freshVar (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb078_alpha_dummy_247 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_244))).fv ∪ ((Class.cv (nb078_alpha_dummy_243))).fv) 0)

noncomputable def nb078_alpha_dummy_248 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_244))).fv ∪ ((Class.cv (nb078_alpha_dummy_243))).fv) 1)

noncomputable def nb078_alpha_dummy_249 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_246 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_245 f))).fv) 0)

noncomputable def nb078_alpha_dummy_250 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_246 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_245 f))).fv) 1)

noncomputable def nb078_alpha_dummy_251 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_247) (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_244)) (Wff.classEq (Class.cv (nb078_alpha_dummy_247)) (syn_cphi (Class.cv (nb078_alpha_dummy_248)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_247) (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_243)) (Wff.classEq (Class.cv (nb078_alpha_dummy_247)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_248))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_252 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_249 f) (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_246 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_249 f) (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_245 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_253 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_247) (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_244)) (Wff.classEq (Class.cv (nb078_alpha_dummy_247)) (syn_cphi (Class.cv (nb078_alpha_dummy_248))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_247) (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_244)) (Wff.classEq (Class.cv (nb078_alpha_dummy_247)) (syn_cphi (Class.cv (nb078_alpha_dummy_248))))))).fv) 0)

noncomputable def nb078_alpha_dummy_254 (f : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_249 f) (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_246 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_249 f) (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_246 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))))))).fv) 0)

noncomputable def nb078_alpha_dummy_255 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_248))).fv) 0)

noncomputable def nb078_alpha_dummy_256 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_248))).fv) 1)

noncomputable def nb078_alpha_dummy_257 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_250 f))).fv) 0)

noncomputable def nb078_alpha_dummy_258 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_250 f))).fv) 1)

noncomputable def nb078_alpha_dummy_259 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_255)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_255)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_255))).fv) 0)

noncomputable def nb078_alpha_dummy_260 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_257 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_257 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_257 f))).fv) 0)

noncomputable def nb078_alpha_dummy_261 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_262 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_263 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_264 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_265 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_266 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_267 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_262)) (Class.cv (nb078_alpha_dummy_263)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_262)) (Class.cv (nb078_alpha_dummy_263)))).fv) 0)

noncomputable def nb078_alpha_dummy_268 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_265 f)) (Class.cv (nb078_alpha_dummy_266 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_265 f)) (Class.cv (nb078_alpha_dummy_266 f)))).fv) 0)

noncomputable def nb078_alpha_dummy_269 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_262))).fv ∪ ((Class.cv (nb078_alpha_dummy_263))).fv) 0)

noncomputable def nb078_alpha_dummy_270 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_265 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_266 f))).fv) 0)

noncomputable def nb078_alpha_dummy_271 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_262)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_263)))).fv) 0)

noncomputable def nb078_alpha_dummy_272 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_265 f)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_266 f)))).fv) 0)

noncomputable def nb078_alpha_dummy_273 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_262))).fv ∪ ((Class.cv (nb078_alpha_dummy_262))).fv) 0)

noncomputable def nb078_alpha_dummy_274 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_265 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_265 f))).fv) 0)

noncomputable def nb078_alpha_dummy_275 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_263))).fv ∪ ((Class.cv (nb078_alpha_dummy_263))).fv) 0)

noncomputable def nb078_alpha_dummy_276 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_266 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_266 f))).fv) 0)

noncomputable def nb078_alpha_dummy_277 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_247) (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_243)) (Wff.classEq (Class.cv (nb078_alpha_dummy_247)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_248))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_247) (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_243)) (Wff.classEq (Class.cv (nb078_alpha_dummy_247)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_248))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_278 (f : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_249 f) (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_245 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_249 f) (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_245 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_279 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_248))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_280 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_281 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_248)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_248)))).fv) 0)

noncomputable def nb078_alpha_dummy_282 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))).fv) 0)

noncomputable def nb078_alpha_dummy_283 : Var := (freshVar (((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_001)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_001)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))) (syn_cid))).fv) 0)

noncomputable def nb078_alpha_dummy_284 (g : Var) : Var := (freshVar (((syn_cnin (syn_ccom (Class.cv g) (syn_ccnv (Class.cv g))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv g) (syn_ccnv (Class.cv g))) (syn_cid))).fv) 0)

noncomputable def nb078_alpha_dummy_285 : Var := (freshVar (((syn_ccom (Class.cv (nb078_alpha_dummy_001)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv ∪ ((syn_cid)).fv) 0)

noncomputable def nb078_alpha_dummy_286 (g : Var) : Var := (freshVar (((syn_ccom (Class.cv g) (syn_ccnv (Class.cv g)))).fv ∪ ((syn_cid)).fv) 0)

noncomputable def nb078_alpha_dummy_287 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) 0)

noncomputable def nb078_alpha_dummy_288 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) 1)

noncomputable def nb078_alpha_dummy_289 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) 2)

noncomputable def nb078_alpha_dummy_290 (g : Var) : Var := (freshVar (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) 0)

noncomputable def nb078_alpha_dummy_291 (g : Var) : Var := (freshVar (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) 1)

noncomputable def nb078_alpha_dummy_292 (g : Var) : Var := (freshVar (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) 2)

noncomputable def nb078_alpha_dummy_293 : Var := (freshVar (({(nb078_alpha_dummy_287)} : Finset Var) ∪ ({(nb078_alpha_dummy_288)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_289) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_287)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_289))) (syn_wbr (Class.cv (nb078_alpha_dummy_289)) (Class.cv (nb078_alpha_dummy_001)) (Class.cv (nb078_alpha_dummy_288)))))).fv) 0)

noncomputable def nb078_alpha_dummy_294 (g : Var) : Var := (freshVar (({(nb078_alpha_dummy_290 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_291 g)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_292 g) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_290 g)) (syn_ccnv (Class.cv g)) (Class.cv (nb078_alpha_dummy_292 g))) (syn_wbr (Class.cv (nb078_alpha_dummy_292 g)) (Class.cv g) (Class.cv (nb078_alpha_dummy_291 g)))))).fv) 0)

noncomputable def nb078_alpha_dummy_295 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) 0)

noncomputable def nb078_alpha_dummy_296 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) 1)

noncomputable def nb078_alpha_dummy_297 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) 0)

noncomputable def nb078_alpha_dummy_298 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) 1)

noncomputable def nb078_alpha_dummy_299 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_295) (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_287)) (Wff.classEq (Class.cv (nb078_alpha_dummy_295)) (syn_cphi (Class.cv (nb078_alpha_dummy_296)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_295) (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_288)) (Wff.classEq (Class.cv (nb078_alpha_dummy_295)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_296))) (syn_csn (syn_c0c)))))))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
