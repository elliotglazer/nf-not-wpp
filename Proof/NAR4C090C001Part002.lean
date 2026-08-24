import NAR4C090C001Part001

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

noncomputable def nb090_alpha_dummy_150 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_151 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_152 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_153 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_154 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_155 (A : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_150 A)) (Class.cv (nb090_alpha_dummy_151 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_150 A)) (Class.cv (nb090_alpha_dummy_151 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_156 (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_153 h)) (Class.cv (nb090_alpha_dummy_154 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_153 h)) (Class.cv (nb090_alpha_dummy_154 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_157 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_150 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_151 A))).fv) 0)

noncomputable def nb090_alpha_dummy_158 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_153 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_154 h))).fv) 0)

noncomputable def nb090_alpha_dummy_159 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_150 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_151 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_160 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_153 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_154 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_161 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_150 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_150 A))).fv) 0)

noncomputable def nb090_alpha_dummy_162 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_153 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_153 h))).fv) 0)

noncomputable def nb090_alpha_dummy_163 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_151 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_151 A))).fv) 0)

noncomputable def nb090_alpha_dummy_164 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_154 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_154 h))).fv) 0)

noncomputable def nb090_alpha_dummy_165 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_135 A) (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_130 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_135 A) (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_130 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_166 (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_137 h) (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_132 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_137 h) (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_132 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_167 (A : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_168 (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_169 (A : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_170 (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_171 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_129 A))).fv) 0)

noncomputable def nb090_alpha_dummy_172 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_129 A))).fv) 1)

noncomputable def nb090_alpha_dummy_173 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv) 0)

noncomputable def nb090_alpha_dummy_174 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv) 1)

noncomputable def nb090_alpha_dummy_175 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_171 A) (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_171 A) (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_129 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_176 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_173 h) (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_173 h) (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_131 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_177 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_171 A) (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_171 A) (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))))).fv) 0)

noncomputable def nb090_alpha_dummy_178 (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_173 h) (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_173 h) (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))))).fv) 0)

noncomputable def nb090_alpha_dummy_179 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_172 A))).fv) 0)

noncomputable def nb090_alpha_dummy_180 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_172 A))).fv) 1)

noncomputable def nb090_alpha_dummy_181 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_174 h))).fv) 0)

noncomputable def nb090_alpha_dummy_182 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_174 h))).fv) 1)

noncomputable def nb090_alpha_dummy_183 (A : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_179 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_179 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_179 A))).fv) 0)

noncomputable def nb090_alpha_dummy_184 (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_181 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_181 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_181 h))).fv) 0)

noncomputable def nb090_alpha_dummy_185 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_186 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_187 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_188 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_189 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_190 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_191 (A : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_186 A)) (Class.cv (nb090_alpha_dummy_187 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_186 A)) (Class.cv (nb090_alpha_dummy_187 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_192 (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_189 h)) (Class.cv (nb090_alpha_dummy_190 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_189 h)) (Class.cv (nb090_alpha_dummy_190 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_193 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_186 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_187 A))).fv) 0)

noncomputable def nb090_alpha_dummy_194 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_189 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_190 h))).fv) 0)

noncomputable def nb090_alpha_dummy_195 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_186 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_187 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_196 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_189 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_190 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_197 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_186 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_186 A))).fv) 0)

noncomputable def nb090_alpha_dummy_198 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_189 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_189 h))).fv) 0)

noncomputable def nb090_alpha_dummy_199 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_187 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_187 A))).fv) 0)

noncomputable def nb090_alpha_dummy_200 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_190 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_190 h))).fv) 0)

noncomputable def nb090_alpha_dummy_201 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_171 A) (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_129 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_171 A) (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_129 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_202 (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_173 h) (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_131 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_173 h) (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_131 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_203 (A : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_204 (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_205 (A : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_206 (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_207 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_051 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) 0)

noncomputable def nb090_alpha_dummy_208 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_051 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) 1)

noncomputable def nb090_alpha_dummy_209 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_054 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) 0)

noncomputable def nb090_alpha_dummy_210 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_054 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) 1)

noncomputable def nb090_alpha_dummy_211 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_207 A) (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_207 A) (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_050 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_212 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_209 h) (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_209 h) (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_053 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_213 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_207 A) (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_207 A) (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))))).fv) 0)

noncomputable def nb090_alpha_dummy_214 (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_209 h) (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_209 h) (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))))).fv) 0)

noncomputable def nb090_alpha_dummy_215 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_208 A))).fv) 0)

noncomputable def nb090_alpha_dummy_216 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_208 A))).fv) 1)

noncomputable def nb090_alpha_dummy_217 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_210 h))).fv) 0)

noncomputable def nb090_alpha_dummy_218 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_210 h))).fv) 1)

noncomputable def nb090_alpha_dummy_219 (A : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_215 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_215 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_215 A))).fv) 0)

noncomputable def nb090_alpha_dummy_220 (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_217 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_217 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_217 h))).fv) 0)

noncomputable def nb090_alpha_dummy_221 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_222 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_223 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_224 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_225 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_226 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_227 (A : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_222 A)) (Class.cv (nb090_alpha_dummy_223 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_222 A)) (Class.cv (nb090_alpha_dummy_223 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_228 (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_225 h)) (Class.cv (nb090_alpha_dummy_226 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_225 h)) (Class.cv (nb090_alpha_dummy_226 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_229 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_222 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_223 A))).fv) 0)

noncomputable def nb090_alpha_dummy_230 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_225 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_226 h))).fv) 0)

noncomputable def nb090_alpha_dummy_231 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_222 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_223 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_232 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_225 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_226 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_233 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_222 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_222 A))).fv) 0)

noncomputable def nb090_alpha_dummy_234 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_225 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_225 h))).fv) 0)

noncomputable def nb090_alpha_dummy_235 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_223 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_223 A))).fv) 0)

noncomputable def nb090_alpha_dummy_236 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_226 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_226 h))).fv) 0)

noncomputable def nb090_alpha_dummy_237 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_207 A) (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_050 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_207 A) (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_050 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_238 (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_209 h) (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_053 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_209 h) (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_053 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_239 (A : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_240 (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_241 (A : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_242 (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_243 (A : Class) : Var := (freshVar (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb090_alpha_dummy_244 (A : Class) : Var := (freshVar (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb090_alpha_dummy_245 (h : Var) : Var := (freshVar (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb090_alpha_dummy_246 (h : Var) : Var := (freshVar (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb090_alpha_dummy_247 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_244 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_243 A))).fv) 0)

noncomputable def nb090_alpha_dummy_248 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_244 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_243 A))).fv) 1)

noncomputable def nb090_alpha_dummy_249 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_246 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_245 h))).fv) 0)

noncomputable def nb090_alpha_dummy_250 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_246 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_245 h))).fv) 1)

noncomputable def nb090_alpha_dummy_251 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_247 A) (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_247 A) (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_243 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_252 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_249 h) (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_246 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_249 h) (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_245 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_253 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_247 A) (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_247 A) (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))))).fv) 0)

noncomputable def nb090_alpha_dummy_254 (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_249 h) (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_246 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_249 h) (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_246 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))))))).fv) 0)

noncomputable def nb090_alpha_dummy_255 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_248 A))).fv) 0)

noncomputable def nb090_alpha_dummy_256 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_248 A))).fv) 1)

noncomputable def nb090_alpha_dummy_257 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_250 h))).fv) 0)

noncomputable def nb090_alpha_dummy_258 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_250 h))).fv) 1)

noncomputable def nb090_alpha_dummy_259 (A : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_255 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_255 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_255 A))).fv) 0)

noncomputable def nb090_alpha_dummy_260 (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_257 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_257 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_257 h))).fv) 0)

noncomputable def nb090_alpha_dummy_261 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_262 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_263 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_264 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_265 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_266 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_267 (A : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_262 A)) (Class.cv (nb090_alpha_dummy_263 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_262 A)) (Class.cv (nb090_alpha_dummy_263 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_268 (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_265 h)) (Class.cv (nb090_alpha_dummy_266 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_265 h)) (Class.cv (nb090_alpha_dummy_266 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_269 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_262 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_263 A))).fv) 0)

noncomputable def nb090_alpha_dummy_270 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_265 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_266 h))).fv) 0)

noncomputable def nb090_alpha_dummy_271 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_262 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_263 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_272 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_265 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_266 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_273 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_262 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_262 A))).fv) 0)

noncomputable def nb090_alpha_dummy_274 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_265 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_265 h))).fv) 0)

noncomputable def nb090_alpha_dummy_275 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_263 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_263 A))).fv) 0)

noncomputable def nb090_alpha_dummy_276 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_266 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_266 h))).fv) 0)

noncomputable def nb090_alpha_dummy_277 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_247 A) (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_243 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_247 A) (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_243 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_278 (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_249 h) (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_245 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_249 h) (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_245 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_279 (A : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_280 (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_281 (A : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_282 (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_283 (A : Class) : Var := (freshVar (((syn_c2nd)).fv ∪ ((Class.cv (nb090_alpha_dummy_001 A))).fv) 0)

noncomputable def nb090_alpha_dummy_284 (u : Var) : Var := (freshVar (((syn_c2nd)).fv ∪ ((Class.cv u)).fv) 0)

noncomputable def nb090_alpha_dummy_285 (A : Class) : Var := (freshVar (({(nb090_alpha_dummy_283 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c2nd) (Class.cv (nb090_alpha_dummy_283 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_286 (u : Var) : Var := (freshVar (({(nb090_alpha_dummy_284 u)} : Finset Var) ∪ ((syn_wbr (Class.cv u) (syn_c2nd) (Class.cv (nb090_alpha_dummy_284 u)))).fv) 0)

noncomputable def nb090_alpha_dummy_287 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_285 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_283 A) (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c2nd) (Class.cv (nb090_alpha_dummy_283 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_285 A)))))).fv) 0)

noncomputable def nb090_alpha_dummy_288 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_285 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_283 A) (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c2nd) (Class.cv (nb090_alpha_dummy_283 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_285 A)))))).fv) 1)

noncomputable def nb090_alpha_dummy_289 (u : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_286 u) (Wff.classEq (Class.cab (nb090_alpha_dummy_284 u) (syn_wbr (Class.cv u) (syn_c2nd) (Class.cv (nb090_alpha_dummy_284 u)))) (syn_csn (Class.cv (nb090_alpha_dummy_286 u)))))).fv) 0)

noncomputable def nb090_alpha_dummy_290 (u : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_286 u) (Wff.classEq (Class.cab (nb090_alpha_dummy_284 u) (syn_wbr (Class.cv u) (syn_c2nd) (Class.cv (nb090_alpha_dummy_284 u)))) (syn_csn (Class.cv (nb090_alpha_dummy_286 u)))))).fv) 1)

noncomputable def nb090_alpha_dummy_291 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_283 A))).fv) 0)

noncomputable def nb090_alpha_dummy_292 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_283 A))).fv) 1)

noncomputable def nb090_alpha_dummy_293 (u : Var) : Var := (freshVar (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv) 0)

noncomputable def nb090_alpha_dummy_294 (u : Var) : Var := (freshVar (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv) 1)

noncomputable def nb090_alpha_dummy_295 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_291 A) (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_291 A) (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_283 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_296 (u : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_293 u) (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u)) (syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_293 u) (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv (nb090_alpha_dummy_284 u)) (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_297 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_291 A) (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_291 A) (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))))))).fv) 0)

noncomputable def nb090_alpha_dummy_298 (u : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_293 u) (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u)) (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_293 u) (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u)) (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))))))).fv) 0)

noncomputable def nb090_alpha_dummy_299 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_292 A))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
