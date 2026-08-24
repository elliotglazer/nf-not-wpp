import NAR4C068C001Part001

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

noncomputable def nb068_alpha_dummy_150 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb068_alpha_dummy_151 : Var := (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_146)) (Class.cv (nb068_alpha_dummy_147)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_146)) (Class.cv (nb068_alpha_dummy_147)))).fv) 0)

noncomputable def nb068_alpha_dummy_152 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_149 f)) (Class.cv (nb068_alpha_dummy_150 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_149 f)) (Class.cv (nb068_alpha_dummy_150 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_153 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_146))).fv ∪ ((Class.cv (nb068_alpha_dummy_147))).fv) 0)

noncomputable def nb068_alpha_dummy_154 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_150 f))).fv) 0)

noncomputable def nb068_alpha_dummy_155 : Var := (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_146)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_147)))).fv) 0)

noncomputable def nb068_alpha_dummy_156 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_149 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_150 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_157 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_146))).fv ∪ ((Class.cv (nb068_alpha_dummy_146))).fv) 0)

noncomputable def nb068_alpha_dummy_158 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_149 f))).fv) 0)

noncomputable def nb068_alpha_dummy_159 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_147))).fv ∪ ((Class.cv (nb068_alpha_dummy_147))).fv) 0)

noncomputable def nb068_alpha_dummy_160 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_150 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_150 f))).fv) 0)

noncomputable def nb068_alpha_dummy_161 : Var := (freshVar (((Class.cab (nb068_alpha_dummy_131) (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126)) (Wff.classEq (Class.cv (nb068_alpha_dummy_131)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_131) (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126)) (Wff.classEq (Class.cv (nb068_alpha_dummy_131)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb068_alpha_dummy_162 (f : Var) : Var := (freshVar (((Class.cab (nb068_alpha_dummy_133 f) (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_133 f) (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb068_alpha_dummy_163 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_132))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb068_alpha_dummy_164 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb068_alpha_dummy_165 : Var := (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_132)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_132)))).fv) 0)

noncomputable def nb068_alpha_dummy_166 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_167 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_126))).fv ∪ ((Class.cv (nb068_alpha_dummy_125))).fv) 0)

noncomputable def nb068_alpha_dummy_168 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_126))).fv ∪ ((Class.cv (nb068_alpha_dummy_125))).fv) 1)

noncomputable def nb068_alpha_dummy_169 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_127 f))).fv) 0)

noncomputable def nb068_alpha_dummy_170 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_127 f))).fv) 1)

noncomputable def nb068_alpha_dummy_171 : Var := (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_167) (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_126)) (Wff.classEq (Class.cv (nb068_alpha_dummy_167)) (syn_cphi (Class.cv (nb068_alpha_dummy_168)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_167) (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125)) (Wff.classEq (Class.cv (nb068_alpha_dummy_167)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb068_alpha_dummy_172 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_169 f) (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_128 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_169 f) (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb068_alpha_dummy_173 : Var := (freshVar (((Class.cab (nb068_alpha_dummy_167) (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_126)) (Wff.classEq (Class.cv (nb068_alpha_dummy_167)) (syn_cphi (Class.cv (nb068_alpha_dummy_168))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_167) (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_126)) (Wff.classEq (Class.cv (nb068_alpha_dummy_167)) (syn_cphi (Class.cv (nb068_alpha_dummy_168))))))).fv) 0)

noncomputable def nb068_alpha_dummy_174 (f : Var) : Var := (freshVar (((Class.cab (nb068_alpha_dummy_169 f) (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_128 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_169 f) (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_128 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))))))).fv) 0)

noncomputable def nb068_alpha_dummy_175 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_168))).fv) 0)

noncomputable def nb068_alpha_dummy_176 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_168))).fv) 1)

noncomputable def nb068_alpha_dummy_177 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_170 f))).fv) 0)

noncomputable def nb068_alpha_dummy_178 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_170 f))).fv) 1)

noncomputable def nb068_alpha_dummy_179 : Var := (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_175)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_175)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_175))).fv) 0)

noncomputable def nb068_alpha_dummy_180 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_177 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_177 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_177 f))).fv) 0)

noncomputable def nb068_alpha_dummy_181 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb068_alpha_dummy_182 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb068_alpha_dummy_183 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb068_alpha_dummy_184 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb068_alpha_dummy_185 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb068_alpha_dummy_186 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb068_alpha_dummy_187 : Var := (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_182)) (Class.cv (nb068_alpha_dummy_183)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_182)) (Class.cv (nb068_alpha_dummy_183)))).fv) 0)

noncomputable def nb068_alpha_dummy_188 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_185 f)) (Class.cv (nb068_alpha_dummy_186 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_185 f)) (Class.cv (nb068_alpha_dummy_186 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_189 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_182))).fv ∪ ((Class.cv (nb068_alpha_dummy_183))).fv) 0)

noncomputable def nb068_alpha_dummy_190 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_186 f))).fv) 0)

noncomputable def nb068_alpha_dummy_191 : Var := (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_182)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_183)))).fv) 0)

noncomputable def nb068_alpha_dummy_192 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_185 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_186 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_193 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_182))).fv ∪ ((Class.cv (nb068_alpha_dummy_182))).fv) 0)

noncomputable def nb068_alpha_dummy_194 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_185 f))).fv) 0)

noncomputable def nb068_alpha_dummy_195 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_183))).fv ∪ ((Class.cv (nb068_alpha_dummy_183))).fv) 0)

noncomputable def nb068_alpha_dummy_196 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_186 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_186 f))).fv) 0)

noncomputable def nb068_alpha_dummy_197 : Var := (freshVar (((Class.cab (nb068_alpha_dummy_167) (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125)) (Wff.classEq (Class.cv (nb068_alpha_dummy_167)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_167) (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125)) (Wff.classEq (Class.cv (nb068_alpha_dummy_167)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb068_alpha_dummy_198 (f : Var) : Var := (freshVar (((Class.cab (nb068_alpha_dummy_169 f) (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_169 f) (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb068_alpha_dummy_199 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_168))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb068_alpha_dummy_200 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb068_alpha_dummy_201 : Var := (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_168)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_168)))).fv) 0)

noncomputable def nb068_alpha_dummy_202 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_203 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_047))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) 0)

noncomputable def nb068_alpha_dummy_204 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_047))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) 1)

noncomputable def nb068_alpha_dummy_205 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_050 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) 0)

noncomputable def nb068_alpha_dummy_206 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_050 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) 1)

noncomputable def nb068_alpha_dummy_207 : Var := (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_203) (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_047)) (Wff.classEq (Class.cv (nb068_alpha_dummy_203)) (syn_cphi (Class.cv (nb068_alpha_dummy_204)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_203) (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_046)) (Wff.classEq (Class.cv (nb068_alpha_dummy_203)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_204))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb068_alpha_dummy_208 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_205 f) (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_050 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_205 f) (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb068_alpha_dummy_209 : Var := (freshVar (((Class.cab (nb068_alpha_dummy_203) (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_047)) (Wff.classEq (Class.cv (nb068_alpha_dummy_203)) (syn_cphi (Class.cv (nb068_alpha_dummy_204))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_203) (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_047)) (Wff.classEq (Class.cv (nb068_alpha_dummy_203)) (syn_cphi (Class.cv (nb068_alpha_dummy_204))))))).fv) 0)

noncomputable def nb068_alpha_dummy_210 (f : Var) : Var := (freshVar (((Class.cab (nb068_alpha_dummy_205 f) (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_050 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_205 f) (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_050 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))))))).fv) 0)

noncomputable def nb068_alpha_dummy_211 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_204))).fv) 0)

noncomputable def nb068_alpha_dummy_212 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_204))).fv) 1)

noncomputable def nb068_alpha_dummy_213 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_206 f))).fv) 0)

noncomputable def nb068_alpha_dummy_214 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_206 f))).fv) 1)

noncomputable def nb068_alpha_dummy_215 : Var := (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_211)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_211)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_211))).fv) 0)

noncomputable def nb068_alpha_dummy_216 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_213 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_213 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_213 f))).fv) 0)

noncomputable def nb068_alpha_dummy_217 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb068_alpha_dummy_218 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb068_alpha_dummy_219 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb068_alpha_dummy_220 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb068_alpha_dummy_221 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb068_alpha_dummy_222 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb068_alpha_dummy_223 : Var := (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_218)) (Class.cv (nb068_alpha_dummy_219)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_218)) (Class.cv (nb068_alpha_dummy_219)))).fv) 0)

noncomputable def nb068_alpha_dummy_224 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_221 f)) (Class.cv (nb068_alpha_dummy_222 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_221 f)) (Class.cv (nb068_alpha_dummy_222 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_225 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_218))).fv ∪ ((Class.cv (nb068_alpha_dummy_219))).fv) 0)

noncomputable def nb068_alpha_dummy_226 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_221 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_222 f))).fv) 0)

noncomputable def nb068_alpha_dummy_227 : Var := (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_218)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_219)))).fv) 0)

noncomputable def nb068_alpha_dummy_228 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_221 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_222 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_229 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_218))).fv ∪ ((Class.cv (nb068_alpha_dummy_218))).fv) 0)

noncomputable def nb068_alpha_dummy_230 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_221 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_221 f))).fv) 0)

noncomputable def nb068_alpha_dummy_231 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_219))).fv ∪ ((Class.cv (nb068_alpha_dummy_219))).fv) 0)

noncomputable def nb068_alpha_dummy_232 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_222 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_222 f))).fv) 0)

noncomputable def nb068_alpha_dummy_233 : Var := (freshVar (((Class.cab (nb068_alpha_dummy_203) (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_046)) (Wff.classEq (Class.cv (nb068_alpha_dummy_203)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_204))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_203) (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_046)) (Wff.classEq (Class.cv (nb068_alpha_dummy_203)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_204))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb068_alpha_dummy_234 (f : Var) : Var := (freshVar (((Class.cab (nb068_alpha_dummy_205 f) (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_205 f) (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb068_alpha_dummy_235 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_204))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb068_alpha_dummy_236 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb068_alpha_dummy_237 : Var := (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_204)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_204)))).fv) 0)

noncomputable def nb068_alpha_dummy_238 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_239 : Var := (freshVar (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb068_alpha_dummy_240 : Var := (freshVar (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb068_alpha_dummy_241 (f : Var) : Var := (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb068_alpha_dummy_242 (f : Var) : Var := (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb068_alpha_dummy_243 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_240))).fv ∪ ((Class.cv (nb068_alpha_dummy_239))).fv) 0)

noncomputable def nb068_alpha_dummy_244 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_240))).fv ∪ ((Class.cv (nb068_alpha_dummy_239))).fv) 1)

noncomputable def nb068_alpha_dummy_245 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_242 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_241 f))).fv) 0)

noncomputable def nb068_alpha_dummy_246 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_242 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_241 f))).fv) 1)

noncomputable def nb068_alpha_dummy_247 : Var := (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_243) (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_240)) (Wff.classEq (Class.cv (nb068_alpha_dummy_243)) (syn_cphi (Class.cv (nb068_alpha_dummy_244)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_243) (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_239)) (Wff.classEq (Class.cv (nb068_alpha_dummy_243)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_244))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb068_alpha_dummy_248 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_245 f) (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_242 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_245 f) (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_241 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb068_alpha_dummy_249 : Var := (freshVar (((Class.cab (nb068_alpha_dummy_243) (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_240)) (Wff.classEq (Class.cv (nb068_alpha_dummy_243)) (syn_cphi (Class.cv (nb068_alpha_dummy_244))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_243) (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_240)) (Wff.classEq (Class.cv (nb068_alpha_dummy_243)) (syn_cphi (Class.cv (nb068_alpha_dummy_244))))))).fv) 0)

noncomputable def nb068_alpha_dummy_250 (f : Var) : Var := (freshVar (((Class.cab (nb068_alpha_dummy_245 f) (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_242 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_245 f) (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_242 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))))))).fv) 0)

noncomputable def nb068_alpha_dummy_251 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_244))).fv) 0)

noncomputable def nb068_alpha_dummy_252 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_244))).fv) 1)

noncomputable def nb068_alpha_dummy_253 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_246 f))).fv) 0)

noncomputable def nb068_alpha_dummy_254 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_246 f))).fv) 1)

noncomputable def nb068_alpha_dummy_255 : Var := (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_251)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_251)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_251))).fv) 0)

noncomputable def nb068_alpha_dummy_256 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_253 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_253 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_253 f))).fv) 0)

noncomputable def nb068_alpha_dummy_257 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb068_alpha_dummy_258 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb068_alpha_dummy_259 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb068_alpha_dummy_260 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb068_alpha_dummy_261 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb068_alpha_dummy_262 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb068_alpha_dummy_263 : Var := (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_258)) (Class.cv (nb068_alpha_dummy_259)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_258)) (Class.cv (nb068_alpha_dummy_259)))).fv) 0)

noncomputable def nb068_alpha_dummy_264 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_261 f)) (Class.cv (nb068_alpha_dummy_262 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_261 f)) (Class.cv (nb068_alpha_dummy_262 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_265 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_258))).fv ∪ ((Class.cv (nb068_alpha_dummy_259))).fv) 0)

noncomputable def nb068_alpha_dummy_266 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_261 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_262 f))).fv) 0)

noncomputable def nb068_alpha_dummy_267 : Var := (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_258)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_259)))).fv) 0)

noncomputable def nb068_alpha_dummy_268 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_261 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_262 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_269 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_258))).fv ∪ ((Class.cv (nb068_alpha_dummy_258))).fv) 0)

noncomputable def nb068_alpha_dummy_270 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_261 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_261 f))).fv) 0)

noncomputable def nb068_alpha_dummy_271 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_259))).fv ∪ ((Class.cv (nb068_alpha_dummy_259))).fv) 0)

noncomputable def nb068_alpha_dummy_272 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_262 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_262 f))).fv) 0)

noncomputable def nb068_alpha_dummy_273 : Var := (freshVar (((Class.cab (nb068_alpha_dummy_243) (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_239)) (Wff.classEq (Class.cv (nb068_alpha_dummy_243)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_244))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_243) (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_239)) (Wff.classEq (Class.cv (nb068_alpha_dummy_243)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_244))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb068_alpha_dummy_274 (f : Var) : Var := (freshVar (((Class.cab (nb068_alpha_dummy_245 f) (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_241 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_245 f) (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_241 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb068_alpha_dummy_275 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_244))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb068_alpha_dummy_276 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb068_alpha_dummy_277 : Var := (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_244)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_244)))).fv) 0)

noncomputable def nb068_alpha_dummy_278 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_279 : Var := (freshVar (((syn_cnin (syn_crn (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_002)))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_002)))).fv) 0)

noncomputable def nb068_alpha_dummy_280 (y : Var) (f : Var) : Var := (freshVar (((syn_cnin (syn_crn (Class.cv f)) (Class.cv y))).fv ∪ ((syn_cnin (syn_crn (Class.cv f)) (Class.cv y))).fv) 0)

noncomputable def nb068_alpha_dummy_281 : Var := (freshVar (((syn_crn (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((Class.cv (nb068_alpha_dummy_002))).fv) 0)

noncomputable def nb068_alpha_dummy_282 (y : Var) (f : Var) : Var := (freshVar (((syn_crn (Class.cv f))).fv ∪ ((Class.cv y)).fv) 0)

noncomputable def nb068_alpha_dummy_283 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb068_alpha_dummy_284 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb068_alpha_dummy_285 (f : Var) : Var := (freshVar (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb068_alpha_dummy_286 (f : Var) : Var := (freshVar (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb068_alpha_dummy_287 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_284))).fv ∪ ((Class.cv (nb068_alpha_dummy_283))).fv) 0)

noncomputable def nb068_alpha_dummy_288 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_284))).fv ∪ ((Class.cv (nb068_alpha_dummy_283))).fv) 1)

noncomputable def nb068_alpha_dummy_289 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_285 f))).fv) 0)

noncomputable def nb068_alpha_dummy_290 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_285 f))).fv) 1)

noncomputable def nb068_alpha_dummy_291 : Var := (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_287) (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_284)) (Wff.classEq (Class.cv (nb068_alpha_dummy_287)) (syn_cphi (Class.cv (nb068_alpha_dummy_288)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_287) (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283)) (Wff.classEq (Class.cv (nb068_alpha_dummy_287)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb068_alpha_dummy_292 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_289 f) (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_286 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_289 f) (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb068_alpha_dummy_293 : Var := (freshVar (((Class.cab (nb068_alpha_dummy_287) (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_284)) (Wff.classEq (Class.cv (nb068_alpha_dummy_287)) (syn_cphi (Class.cv (nb068_alpha_dummy_288))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_287) (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_284)) (Wff.classEq (Class.cv (nb068_alpha_dummy_287)) (syn_cphi (Class.cv (nb068_alpha_dummy_288))))))).fv) 0)

noncomputable def nb068_alpha_dummy_294 (f : Var) : Var := (freshVar (((Class.cab (nb068_alpha_dummy_289 f) (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_286 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_289 f) (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_286 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))))))).fv) 0)

noncomputable def nb068_alpha_dummy_295 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_288))).fv) 0)

noncomputable def nb068_alpha_dummy_296 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_288))).fv) 1)

noncomputable def nb068_alpha_dummy_297 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_290 f))).fv) 0)

noncomputable def nb068_alpha_dummy_298 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_290 f))).fv) 1)

noncomputable def nb068_alpha_dummy_299 : Var := (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_295)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_295)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_295))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
