import NAR4C067C001Part001

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

noncomputable def nb067_alpha_dummy_150 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_146 f))).fv) 0)

noncomputable def nb067_alpha_dummy_151 : Var := (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_142)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_143)))).fv) 0)

noncomputable def nb067_alpha_dummy_152 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_145 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_146 f)))).fv) 0)

noncomputable def nb067_alpha_dummy_153 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_142))).fv ∪ ((Class.cv (nb067_alpha_dummy_142))).fv) 0)

noncomputable def nb067_alpha_dummy_154 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_145 f))).fv) 0)

noncomputable def nb067_alpha_dummy_155 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_143))).fv ∪ ((Class.cv (nb067_alpha_dummy_143))).fv) 0)

noncomputable def nb067_alpha_dummy_156 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_146 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_146 f))).fv) 0)

noncomputable def nb067_alpha_dummy_157 : Var := (freshVar (((Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb067_alpha_dummy_158 (f : Var) : Var := (freshVar (((Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb067_alpha_dummy_159 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_128))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb067_alpha_dummy_160 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb067_alpha_dummy_161 : Var := (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_128)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_128)))).fv) 0)

noncomputable def nb067_alpha_dummy_162 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))).fv) 0)

noncomputable def nb067_alpha_dummy_163 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_000))).fv) 0)

noncomputable def nb067_alpha_dummy_164 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_000))).fv) 1)

noncomputable def nb067_alpha_dummy_165 (f : Var) : Var := (freshVar (((Class.cv f)).fv) 0)

noncomputable def nb067_alpha_dummy_166 (f : Var) : Var := (freshVar (((Class.cv f)).fv) 1)

noncomputable def nb067_alpha_dummy_167 : Var := (freshVar (({(nb067_alpha_dummy_163)} : Finset Var) ∪ ({(nb067_alpha_dummy_164)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb067_alpha_dummy_164)) (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_163)))).fv) 0)

noncomputable def nb067_alpha_dummy_168 (f : Var) : Var := (freshVar (({(nb067_alpha_dummy_165 f)} : Finset Var) ∪ ({(nb067_alpha_dummy_166 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb067_alpha_dummy_166 f)) (Class.cv f) (Class.cv (nb067_alpha_dummy_165 f)))).fv) 0)

noncomputable def nb067_alpha_dummy_169 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_163))).fv ∪ ((Class.cv (nb067_alpha_dummy_164))).fv) 0)

noncomputable def nb067_alpha_dummy_170 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_163))).fv ∪ ((Class.cv (nb067_alpha_dummy_164))).fv) 1)

noncomputable def nb067_alpha_dummy_171 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_166 f))).fv) 0)

noncomputable def nb067_alpha_dummy_172 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_166 f))).fv) 1)

noncomputable def nb067_alpha_dummy_173 : Var := (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cphi (Class.cv (nb067_alpha_dummy_170)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb067_alpha_dummy_174 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb067_alpha_dummy_175 : Var := (freshVar (((Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cphi (Class.cv (nb067_alpha_dummy_170))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cphi (Class.cv (nb067_alpha_dummy_170))))))).fv) 0)

noncomputable def nb067_alpha_dummy_176 (f : Var) : Var := (freshVar (((Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))))))).fv) 0)

noncomputable def nb067_alpha_dummy_177 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_170))).fv) 0)

noncomputable def nb067_alpha_dummy_178 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_170))).fv) 1)

noncomputable def nb067_alpha_dummy_179 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_172 f))).fv) 0)

noncomputable def nb067_alpha_dummy_180 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_172 f))).fv) 1)

noncomputable def nb067_alpha_dummy_181 : Var := (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_177)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_177)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_177))).fv) 0)

noncomputable def nb067_alpha_dummy_182 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_179 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_179 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_179 f))).fv) 0)

noncomputable def nb067_alpha_dummy_183 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb067_alpha_dummy_184 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb067_alpha_dummy_185 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb067_alpha_dummy_186 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb067_alpha_dummy_187 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb067_alpha_dummy_188 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb067_alpha_dummy_189 : Var := (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185)))).fv) 0)

noncomputable def nb067_alpha_dummy_190 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_187 f)) (Class.cv (nb067_alpha_dummy_188 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_187 f)) (Class.cv (nb067_alpha_dummy_188 f)))).fv) 0)

noncomputable def nb067_alpha_dummy_191 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_184))).fv ∪ ((Class.cv (nb067_alpha_dummy_185))).fv) 0)

noncomputable def nb067_alpha_dummy_192 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_187 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_188 f))).fv) 0)

noncomputable def nb067_alpha_dummy_193 : Var := (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_184)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_185)))).fv) 0)

noncomputable def nb067_alpha_dummy_194 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_187 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_188 f)))).fv) 0)

noncomputable def nb067_alpha_dummy_195 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_184))).fv ∪ ((Class.cv (nb067_alpha_dummy_184))).fv) 0)

noncomputable def nb067_alpha_dummy_196 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_187 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_187 f))).fv) 0)

noncomputable def nb067_alpha_dummy_197 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_185))).fv ∪ ((Class.cv (nb067_alpha_dummy_185))).fv) 0)

noncomputable def nb067_alpha_dummy_198 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_188 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_188 f))).fv) 0)

noncomputable def nb067_alpha_dummy_199 : Var := (freshVar (((Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb067_alpha_dummy_200 (f : Var) : Var := (freshVar (((Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb067_alpha_dummy_201 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_170))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb067_alpha_dummy_202 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb067_alpha_dummy_203 : Var := (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_170)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_170)))).fv) 0)

noncomputable def nb067_alpha_dummy_204 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))).fv) 0)

noncomputable def nb067_alpha_dummy_205 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_164))).fv ∪ ((Class.cv (nb067_alpha_dummy_163))).fv) 0)

noncomputable def nb067_alpha_dummy_206 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_164))).fv ∪ ((Class.cv (nb067_alpha_dummy_163))).fv) 1)

noncomputable def nb067_alpha_dummy_207 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_165 f))).fv) 0)

noncomputable def nb067_alpha_dummy_208 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_165 f))).fv) 1)

noncomputable def nb067_alpha_dummy_209 : Var := (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cphi (Class.cv (nb067_alpha_dummy_206)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb067_alpha_dummy_210 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb067_alpha_dummy_211 : Var := (freshVar (((Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cphi (Class.cv (nb067_alpha_dummy_206))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cphi (Class.cv (nb067_alpha_dummy_206))))))).fv) 0)

noncomputable def nb067_alpha_dummy_212 (f : Var) : Var := (freshVar (((Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))))))).fv) 0)

noncomputable def nb067_alpha_dummy_213 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_206))).fv) 0)

noncomputable def nb067_alpha_dummy_214 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_206))).fv) 1)

noncomputable def nb067_alpha_dummy_215 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_208 f))).fv) 0)

noncomputable def nb067_alpha_dummy_216 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_208 f))).fv) 1)

noncomputable def nb067_alpha_dummy_217 : Var := (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_213)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_213)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_213))).fv) 0)

noncomputable def nb067_alpha_dummy_218 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_215 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_215 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_215 f))).fv) 0)

noncomputable def nb067_alpha_dummy_219 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb067_alpha_dummy_220 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb067_alpha_dummy_221 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb067_alpha_dummy_222 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb067_alpha_dummy_223 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb067_alpha_dummy_224 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb067_alpha_dummy_225 : Var := (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221)))).fv) 0)

noncomputable def nb067_alpha_dummy_226 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_223 f)) (Class.cv (nb067_alpha_dummy_224 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_223 f)) (Class.cv (nb067_alpha_dummy_224 f)))).fv) 0)

noncomputable def nb067_alpha_dummy_227 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_220))).fv ∪ ((Class.cv (nb067_alpha_dummy_221))).fv) 0)

noncomputable def nb067_alpha_dummy_228 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_223 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_224 f))).fv) 0)

noncomputable def nb067_alpha_dummy_229 : Var := (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_220)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_221)))).fv) 0)

noncomputable def nb067_alpha_dummy_230 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_223 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_224 f)))).fv) 0)

noncomputable def nb067_alpha_dummy_231 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_220))).fv ∪ ((Class.cv (nb067_alpha_dummy_220))).fv) 0)

noncomputable def nb067_alpha_dummy_232 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_223 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_223 f))).fv) 0)

noncomputable def nb067_alpha_dummy_233 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_221))).fv ∪ ((Class.cv (nb067_alpha_dummy_221))).fv) 0)

noncomputable def nb067_alpha_dummy_234 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_224 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_224 f))).fv) 0)

noncomputable def nb067_alpha_dummy_235 : Var := (freshVar (((Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb067_alpha_dummy_236 (f : Var) : Var := (freshVar (((Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb067_alpha_dummy_237 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_206))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb067_alpha_dummy_238 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb067_alpha_dummy_239 : Var := (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_206)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_206)))).fv) 0)

noncomputable def nb067_alpha_dummy_240 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))).fv) 0)

noncomputable def nb067_alpha_dummy_241 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_085))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) 0)

noncomputable def nb067_alpha_dummy_242 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_085))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) 1)

noncomputable def nb067_alpha_dummy_243 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) 0)

noncomputable def nb067_alpha_dummy_244 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) 1)

noncomputable def nb067_alpha_dummy_245 : Var := (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cphi (Class.cv (nb067_alpha_dummy_242)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb067_alpha_dummy_246 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb067_alpha_dummy_247 : Var := (freshVar (((Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cphi (Class.cv (nb067_alpha_dummy_242))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cphi (Class.cv (nb067_alpha_dummy_242))))))).fv) 0)

noncomputable def nb067_alpha_dummy_248 (f : Var) : Var := (freshVar (((Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))))))).fv) 0)

noncomputable def nb067_alpha_dummy_249 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_242))).fv) 0)

noncomputable def nb067_alpha_dummy_250 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_242))).fv) 1)

noncomputable def nb067_alpha_dummy_251 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_244 f))).fv) 0)

noncomputable def nb067_alpha_dummy_252 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_244 f))).fv) 1)

noncomputable def nb067_alpha_dummy_253 : Var := (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_249)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_249)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_249))).fv) 0)

noncomputable def nb067_alpha_dummy_254 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_251 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_251 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_251 f))).fv) 0)

noncomputable def nb067_alpha_dummy_255 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb067_alpha_dummy_256 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb067_alpha_dummy_257 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb067_alpha_dummy_258 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb067_alpha_dummy_259 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb067_alpha_dummy_260 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb067_alpha_dummy_261 : Var := (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_256)) (Class.cv (nb067_alpha_dummy_257)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_256)) (Class.cv (nb067_alpha_dummy_257)))).fv) 0)

noncomputable def nb067_alpha_dummy_262 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_259 f)) (Class.cv (nb067_alpha_dummy_260 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_259 f)) (Class.cv (nb067_alpha_dummy_260 f)))).fv) 0)

noncomputable def nb067_alpha_dummy_263 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_256))).fv ∪ ((Class.cv (nb067_alpha_dummy_257))).fv) 0)

noncomputable def nb067_alpha_dummy_264 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_259 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_260 f))).fv) 0)

noncomputable def nb067_alpha_dummy_265 : Var := (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_256)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_257)))).fv) 0)

noncomputable def nb067_alpha_dummy_266 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_259 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_260 f)))).fv) 0)

noncomputable def nb067_alpha_dummy_267 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_256))).fv ∪ ((Class.cv (nb067_alpha_dummy_256))).fv) 0)

noncomputable def nb067_alpha_dummy_268 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_259 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_259 f))).fv) 0)

noncomputable def nb067_alpha_dummy_269 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_257))).fv ∪ ((Class.cv (nb067_alpha_dummy_257))).fv) 0)

noncomputable def nb067_alpha_dummy_270 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_260 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_260 f))).fv) 0)

noncomputable def nb067_alpha_dummy_271 : Var := (freshVar (((Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb067_alpha_dummy_272 (f : Var) : Var := (freshVar (((Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb067_alpha_dummy_273 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_242))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb067_alpha_dummy_274 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb067_alpha_dummy_275 : Var := (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_242)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_242)))).fv) 0)

noncomputable def nb067_alpha_dummy_276 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))).fv) 0)

noncomputable def nb067_alpha_dummy_277 : Var := (freshVar (((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb067_alpha_dummy_278 : Var := (freshVar (((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb067_alpha_dummy_279 (f : Var) : Var := (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb067_alpha_dummy_280 (f : Var) : Var := (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb067_alpha_dummy_281 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_278))).fv ∪ ((Class.cv (nb067_alpha_dummy_277))).fv) 0)

noncomputable def nb067_alpha_dummy_282 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_278))).fv ∪ ((Class.cv (nb067_alpha_dummy_277))).fv) 1)

noncomputable def nb067_alpha_dummy_283 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_280 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_279 f))).fv) 0)

noncomputable def nb067_alpha_dummy_284 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_280 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_279 f))).fv) 1)

noncomputable def nb067_alpha_dummy_285 : Var := (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cphi (Class.cv (nb067_alpha_dummy_282)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb067_alpha_dummy_286 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb067_alpha_dummy_287 : Var := (freshVar (((Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cphi (Class.cv (nb067_alpha_dummy_282))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cphi (Class.cv (nb067_alpha_dummy_282))))))).fv) 0)

noncomputable def nb067_alpha_dummy_288 (f : Var) : Var := (freshVar (((Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))))))).fv) 0)

noncomputable def nb067_alpha_dummy_289 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_282))).fv) 0)

noncomputable def nb067_alpha_dummy_290 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_282))).fv) 1)

noncomputable def nb067_alpha_dummy_291 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_284 f))).fv) 0)

noncomputable def nb067_alpha_dummy_292 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_284 f))).fv) 1)

noncomputable def nb067_alpha_dummy_293 : Var := (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_289)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_289)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_289))).fv) 0)

noncomputable def nb067_alpha_dummy_294 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_291 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_291 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_291 f))).fv) 0)

noncomputable def nb067_alpha_dummy_295 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb067_alpha_dummy_296 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb067_alpha_dummy_297 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb067_alpha_dummy_298 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb067_alpha_dummy_299 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) 1)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
