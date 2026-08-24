import NAR4C057C001Part001

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

noncomputable def nb057_alpha_dummy_150 : Var := (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146)))).fv) 0)

noncomputable def nb057_alpha_dummy_151 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_148 f)) (Class.cv (nb057_alpha_dummy_149 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_148 f)) (Class.cv (nb057_alpha_dummy_149 f)))).fv) 0)

noncomputable def nb057_alpha_dummy_152 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_145))).fv ∪ ((Class.cv (nb057_alpha_dummy_146))).fv) 0)

noncomputable def nb057_alpha_dummy_153 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_148 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_149 f))).fv) 0)

noncomputable def nb057_alpha_dummy_154 : Var := (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_145)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_146)))).fv) 0)

noncomputable def nb057_alpha_dummy_155 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_148 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_149 f)))).fv) 0)

noncomputable def nb057_alpha_dummy_156 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_145))).fv ∪ ((Class.cv (nb057_alpha_dummy_145))).fv) 0)

noncomputable def nb057_alpha_dummy_157 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_148 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_148 f))).fv) 0)

noncomputable def nb057_alpha_dummy_158 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_146))).fv ∪ ((Class.cv (nb057_alpha_dummy_146))).fv) 0)

noncomputable def nb057_alpha_dummy_159 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_149 f))).fv) 0)

noncomputable def nb057_alpha_dummy_160 : Var := (freshVar (((Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb057_alpha_dummy_161 (f : Var) : Var := (freshVar (((Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb057_alpha_dummy_162 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_131))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb057_alpha_dummy_163 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb057_alpha_dummy_164 : Var := (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_131)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_131)))).fv) 0)

noncomputable def nb057_alpha_dummy_165 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))).fv) 0)

noncomputable def nb057_alpha_dummy_166 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_125))).fv ∪ ((Class.cv (nb057_alpha_dummy_124))).fv) 0)

noncomputable def nb057_alpha_dummy_167 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_125))).fv ∪ ((Class.cv (nb057_alpha_dummy_124))).fv) 1)

noncomputable def nb057_alpha_dummy_168 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_126 f))).fv) 0)

noncomputable def nb057_alpha_dummy_169 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_126 f))).fv) 1)

noncomputable def nb057_alpha_dummy_170 : Var := (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cphi (Class.cv (nb057_alpha_dummy_167)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb057_alpha_dummy_171 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb057_alpha_dummy_172 : Var := (freshVar (((Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cphi (Class.cv (nb057_alpha_dummy_167))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cphi (Class.cv (nb057_alpha_dummy_167))))))).fv) 0)

noncomputable def nb057_alpha_dummy_173 (f : Var) : Var := (freshVar (((Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))))))).fv) 0)

noncomputable def nb057_alpha_dummy_174 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_167))).fv) 0)

noncomputable def nb057_alpha_dummy_175 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_167))).fv) 1)

noncomputable def nb057_alpha_dummy_176 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_169 f))).fv) 0)

noncomputable def nb057_alpha_dummy_177 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_169 f))).fv) 1)

noncomputable def nb057_alpha_dummy_178 : Var := (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_174)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_174)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_174))).fv) 0)

noncomputable def nb057_alpha_dummy_179 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_176 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_176 f)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_176 f))).fv) 0)

noncomputable def nb057_alpha_dummy_180 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb057_alpha_dummy_181 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb057_alpha_dummy_182 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb057_alpha_dummy_183 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb057_alpha_dummy_184 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb057_alpha_dummy_185 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb057_alpha_dummy_186 : Var := (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_181)) (Class.cv (nb057_alpha_dummy_182)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_181)) (Class.cv (nb057_alpha_dummy_182)))).fv) 0)

noncomputable def nb057_alpha_dummy_187 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_184 f)) (Class.cv (nb057_alpha_dummy_185 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_184 f)) (Class.cv (nb057_alpha_dummy_185 f)))).fv) 0)

noncomputable def nb057_alpha_dummy_188 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_181))).fv ∪ ((Class.cv (nb057_alpha_dummy_182))).fv) 0)

noncomputable def nb057_alpha_dummy_189 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_184 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_185 f))).fv) 0)

noncomputable def nb057_alpha_dummy_190 : Var := (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_181)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_182)))).fv) 0)

noncomputable def nb057_alpha_dummy_191 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_184 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_185 f)))).fv) 0)

noncomputable def nb057_alpha_dummy_192 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_181))).fv ∪ ((Class.cv (nb057_alpha_dummy_181))).fv) 0)

noncomputable def nb057_alpha_dummy_193 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_184 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_184 f))).fv) 0)

noncomputable def nb057_alpha_dummy_194 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_182))).fv ∪ ((Class.cv (nb057_alpha_dummy_182))).fv) 0)

noncomputable def nb057_alpha_dummy_195 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_185 f))).fv) 0)

noncomputable def nb057_alpha_dummy_196 : Var := (freshVar (((Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb057_alpha_dummy_197 (f : Var) : Var := (freshVar (((Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb057_alpha_dummy_198 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_167))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb057_alpha_dummy_199 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb057_alpha_dummy_200 : Var := (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_167)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_167)))).fv) 0)

noncomputable def nb057_alpha_dummy_201 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))).fv) 0)

noncomputable def nb057_alpha_dummy_202 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_046))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) 0)

noncomputable def nb057_alpha_dummy_203 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_046))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) 1)

noncomputable def nb057_alpha_dummy_204 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) 0)

noncomputable def nb057_alpha_dummy_205 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) 1)

noncomputable def nb057_alpha_dummy_206 : Var := (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cphi (Class.cv (nb057_alpha_dummy_203)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb057_alpha_dummy_207 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb057_alpha_dummy_208 : Var := (freshVar (((Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cphi (Class.cv (nb057_alpha_dummy_203))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cphi (Class.cv (nb057_alpha_dummy_203))))))).fv) 0)

noncomputable def nb057_alpha_dummy_209 (f : Var) : Var := (freshVar (((Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))))))).fv) 0)

noncomputable def nb057_alpha_dummy_210 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_203))).fv) 0)

noncomputable def nb057_alpha_dummy_211 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_203))).fv) 1)

noncomputable def nb057_alpha_dummy_212 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_205 f))).fv) 0)

noncomputable def nb057_alpha_dummy_213 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_205 f))).fv) 1)

noncomputable def nb057_alpha_dummy_214 : Var := (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_210)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_210)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_210))).fv) 0)

noncomputable def nb057_alpha_dummy_215 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_212 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_212 f)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_212 f))).fv) 0)

noncomputable def nb057_alpha_dummy_216 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb057_alpha_dummy_217 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb057_alpha_dummy_218 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb057_alpha_dummy_219 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb057_alpha_dummy_220 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb057_alpha_dummy_221 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb057_alpha_dummy_222 : Var := (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_217)) (Class.cv (nb057_alpha_dummy_218)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_217)) (Class.cv (nb057_alpha_dummy_218)))).fv) 0)

noncomputable def nb057_alpha_dummy_223 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_220 f)) (Class.cv (nb057_alpha_dummy_221 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_220 f)) (Class.cv (nb057_alpha_dummy_221 f)))).fv) 0)

noncomputable def nb057_alpha_dummy_224 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_217))).fv ∪ ((Class.cv (nb057_alpha_dummy_218))).fv) 0)

noncomputable def nb057_alpha_dummy_225 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_220 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_221 f))).fv) 0)

noncomputable def nb057_alpha_dummy_226 : Var := (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_217)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_218)))).fv) 0)

noncomputable def nb057_alpha_dummy_227 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_220 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_221 f)))).fv) 0)

noncomputable def nb057_alpha_dummy_228 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_217))).fv ∪ ((Class.cv (nb057_alpha_dummy_217))).fv) 0)

noncomputable def nb057_alpha_dummy_229 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_220 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_220 f))).fv) 0)

noncomputable def nb057_alpha_dummy_230 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_218))).fv ∪ ((Class.cv (nb057_alpha_dummy_218))).fv) 0)

noncomputable def nb057_alpha_dummy_231 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_221 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_221 f))).fv) 0)

noncomputable def nb057_alpha_dummy_232 : Var := (freshVar (((Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb057_alpha_dummy_233 (f : Var) : Var := (freshVar (((Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb057_alpha_dummy_234 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_203))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb057_alpha_dummy_235 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb057_alpha_dummy_236 : Var := (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_203)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_203)))).fv) 0)

noncomputable def nb057_alpha_dummy_237 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))).fv) 0)

noncomputable def nb057_alpha_dummy_238 : Var := (freshVar (((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb057_alpha_dummy_239 : Var := (freshVar (((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb057_alpha_dummy_240 (f : Var) : Var := (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb057_alpha_dummy_241 (f : Var) : Var := (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb057_alpha_dummy_242 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_239))).fv ∪ ((Class.cv (nb057_alpha_dummy_238))).fv) 0)

noncomputable def nb057_alpha_dummy_243 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_239))).fv ∪ ((Class.cv (nb057_alpha_dummy_238))).fv) 1)

noncomputable def nb057_alpha_dummy_244 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_241 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_240 f))).fv) 0)

noncomputable def nb057_alpha_dummy_245 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_241 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_240 f))).fv) 1)

noncomputable def nb057_alpha_dummy_246 : Var := (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cphi (Class.cv (nb057_alpha_dummy_243)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb057_alpha_dummy_247 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb057_alpha_dummy_248 : Var := (freshVar (((Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cphi (Class.cv (nb057_alpha_dummy_243))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cphi (Class.cv (nb057_alpha_dummy_243))))))).fv) 0)

noncomputable def nb057_alpha_dummy_249 (f : Var) : Var := (freshVar (((Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))))))).fv) 0)

noncomputable def nb057_alpha_dummy_250 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_243))).fv) 0)

noncomputable def nb057_alpha_dummy_251 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_243))).fv) 1)

noncomputable def nb057_alpha_dummy_252 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_245 f))).fv) 0)

noncomputable def nb057_alpha_dummy_253 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_245 f))).fv) 1)

noncomputable def nb057_alpha_dummy_254 : Var := (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_250)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_250)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_250))).fv) 0)

noncomputable def nb057_alpha_dummy_255 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_252 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_252 f)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_252 f))).fv) 0)

noncomputable def nb057_alpha_dummy_256 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb057_alpha_dummy_257 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb057_alpha_dummy_258 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb057_alpha_dummy_259 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb057_alpha_dummy_260 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb057_alpha_dummy_261 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb057_alpha_dummy_262 : Var := (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_257)) (Class.cv (nb057_alpha_dummy_258)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_257)) (Class.cv (nb057_alpha_dummy_258)))).fv) 0)

noncomputable def nb057_alpha_dummy_263 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_260 f)) (Class.cv (nb057_alpha_dummy_261 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_260 f)) (Class.cv (nb057_alpha_dummy_261 f)))).fv) 0)

noncomputable def nb057_alpha_dummy_264 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_257))).fv ∪ ((Class.cv (nb057_alpha_dummy_258))).fv) 0)

noncomputable def nb057_alpha_dummy_265 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_260 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_261 f))).fv) 0)

noncomputable def nb057_alpha_dummy_266 : Var := (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_257)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_258)))).fv) 0)

noncomputable def nb057_alpha_dummy_267 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_260 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_261 f)))).fv) 0)

noncomputable def nb057_alpha_dummy_268 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_257))).fv ∪ ((Class.cv (nb057_alpha_dummy_257))).fv) 0)

noncomputable def nb057_alpha_dummy_269 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_260 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_260 f))).fv) 0)

noncomputable def nb057_alpha_dummy_270 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_258))).fv ∪ ((Class.cv (nb057_alpha_dummy_258))).fv) 0)

noncomputable def nb057_alpha_dummy_271 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_261 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_261 f))).fv) 0)

noncomputable def nb057_alpha_dummy_272 : Var := (freshVar (((Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb057_alpha_dummy_273 (f : Var) : Var := (freshVar (((Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb057_alpha_dummy_274 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_243))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb057_alpha_dummy_275 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb057_alpha_dummy_276 : Var := (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_243)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_243)))).fv) 0)

noncomputable def nb057_alpha_dummy_277 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))).fv) 0)

theorem nb057_fresh_000 : (nb057_alpha_dummy_034) ∉ (((Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb057_alpha_dummy_034] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb057_fresh_001 : (nb057_alpha_dummy_010) ∉ (((Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cphi (Class.cv (nb057_alpha_dummy_005))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cphi (Class.cv (nb057_alpha_dummy_005))))))).fv) := by
  simpa only [nb057_alpha_dummy_010] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cphi (Class.cv (nb057_alpha_dummy_005))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cphi (Class.cv (nb057_alpha_dummy_005))))))).fv) 0

theorem nb057_fresh_002 (f : Var) (a : Var) : (nb057_alpha_dummy_035 f a) ∉ (((Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb057_alpha_dummy_035] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb057_fresh_003 (f : Var) (a : Var) : (nb057_alpha_dummy_011 f a) ∉ (((Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))))))).fv) := by
  simpa only [nb057_alpha_dummy_011] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))))))).fv) 0

theorem nb057_fresh_004 : (nb057_alpha_dummy_058) ∉ (((Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cphi (Class.cv (nb057_alpha_dummy_053))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cphi (Class.cv (nb057_alpha_dummy_053))))))).fv) := by
  simpa only [nb057_alpha_dummy_058] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cphi (Class.cv (nb057_alpha_dummy_053))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cphi (Class.cv (nb057_alpha_dummy_053))))))).fv) 0

theorem nb057_fresh_005 : (nb057_alpha_dummy_082) ∉ (((Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb057_alpha_dummy_082] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb057_fresh_006 (f : Var) : (nb057_alpha_dummy_059 f) ∉ (((Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))))))).fv) := by
  simpa only [nb057_alpha_dummy_059] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))))))).fv) 0

theorem nb057_fresh_007 (f : Var) : (nb057_alpha_dummy_083 f) ∉ (((Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb057_alpha_dummy_083] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb057_fresh_008 : (nb057_alpha_dummy_094) ∉ (((Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cphi (Class.cv (nb057_alpha_dummy_089))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cphi (Class.cv (nb057_alpha_dummy_089))))))).fv) := by
  simpa only [nb057_alpha_dummy_094] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cphi (Class.cv (nb057_alpha_dummy_089))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cphi (Class.cv (nb057_alpha_dummy_089))))))).fv) 0

theorem nb057_fresh_009 : (nb057_alpha_dummy_118) ∉ (((Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb057_alpha_dummy_118] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb057_fresh_010 (f : Var) : (nb057_alpha_dummy_095 f) ∉ (((Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))))))).fv) := by
  simpa only [nb057_alpha_dummy_095] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))))))).fv) 0

theorem nb057_fresh_011 (f : Var) : (nb057_alpha_dummy_119 f) ∉ (((Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb057_alpha_dummy_119] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb057_fresh_012 : (nb057_alpha_dummy_136) ∉ (((Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cphi (Class.cv (nb057_alpha_dummy_131))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cphi (Class.cv (nb057_alpha_dummy_131))))))).fv) := by
  simpa only [nb057_alpha_dummy_136] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cphi (Class.cv (nb057_alpha_dummy_131))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cphi (Class.cv (nb057_alpha_dummy_131))))))).fv) 0

theorem nb057_fresh_013 : (nb057_alpha_dummy_160) ∉ (((Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb057_alpha_dummy_160] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb057_fresh_014 (f : Var) : (nb057_alpha_dummy_137 f) ∉ (((Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))))))).fv) := by
  simpa only [nb057_alpha_dummy_137] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))))))).fv) 0

theorem nb057_fresh_015 (f : Var) : (nb057_alpha_dummy_161 f) ∉ (((Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb057_alpha_dummy_161] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb057_fresh_016 : (nb057_alpha_dummy_196) ∉ (((Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb057_alpha_dummy_196] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb057_fresh_017 : (nb057_alpha_dummy_172) ∉ (((Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cphi (Class.cv (nb057_alpha_dummy_167))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cphi (Class.cv (nb057_alpha_dummy_167))))))).fv) := by
  simpa only [nb057_alpha_dummy_172] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cphi (Class.cv (nb057_alpha_dummy_167))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cphi (Class.cv (nb057_alpha_dummy_167))))))).fv) 0

theorem nb057_fresh_018 (f : Var) : (nb057_alpha_dummy_197 f) ∉ (((Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb057_alpha_dummy_197] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb057_fresh_019 (f : Var) : (nb057_alpha_dummy_173 f) ∉ (((Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))))))).fv) := by
  simpa only [nb057_alpha_dummy_173] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))))))).fv) 0

theorem nb057_fresh_020 : (nb057_alpha_dummy_232) ∉ (((Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb057_alpha_dummy_232] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb057_fresh_021 : (nb057_alpha_dummy_208) ∉ (((Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cphi (Class.cv (nb057_alpha_dummy_203))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cphi (Class.cv (nb057_alpha_dummy_203))))))).fv) := by
  simpa only [nb057_alpha_dummy_208] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cphi (Class.cv (nb057_alpha_dummy_203))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cphi (Class.cv (nb057_alpha_dummy_203))))))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
