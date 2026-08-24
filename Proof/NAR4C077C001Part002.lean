import NAR4C077C001Part001

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

noncomputable def nb077_alpha_dummy_150 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) 1)

noncomputable def nb077_alpha_dummy_151 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb077_alpha_dummy_152 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb077_alpha_dummy_153 (F : Class) (I : Class) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))))).fv) 0)

noncomputable def nb077_alpha_dummy_154 (x : Var) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))))).fv) 0)

noncomputable def nb077_alpha_dummy_155 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_148 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_156 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_148 F I))).fv) 1)

noncomputable def nb077_alpha_dummy_157 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_150 x))).fv) 0)

noncomputable def nb077_alpha_dummy_158 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_150 x))).fv) 1)

noncomputable def nb077_alpha_dummy_159 (F : Class) (I : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_155 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_155 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_155 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_160 (x : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_157 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_157 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_157 x))).fv) 0)

noncomputable def nb077_alpha_dummy_161 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb077_alpha_dummy_162 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb077_alpha_dummy_163 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb077_alpha_dummy_164 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb077_alpha_dummy_165 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb077_alpha_dummy_166 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb077_alpha_dummy_167 (F : Class) (I : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_162 F I)) (Class.cv (nb077_alpha_dummy_163 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_162 F I)) (Class.cv (nb077_alpha_dummy_163 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_168 (x : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_165 x)) (Class.cv (nb077_alpha_dummy_166 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_165 x)) (Class.cv (nb077_alpha_dummy_166 x)))).fv) 0)

noncomputable def nb077_alpha_dummy_169 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_162 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_163 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_170 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_165 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_166 x))).fv) 0)

noncomputable def nb077_alpha_dummy_171 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_162 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_163 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_172 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_165 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_166 x)))).fv) 0)

noncomputable def nb077_alpha_dummy_173 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_162 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_162 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_174 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_165 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_165 x))).fv) 0)

noncomputable def nb077_alpha_dummy_175 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_163 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_163 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_176 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_166 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_166 x))).fv) 0)

noncomputable def nb077_alpha_dummy_177 (F : Class) (I : Class) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb077_alpha_dummy_178 (x : Var) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb077_alpha_dummy_179 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb077_alpha_dummy_180 (x : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb077_alpha_dummy_181 (F : Class) (I : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_182 (x : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))).fv) 0)

noncomputable def nb077_alpha_dummy_183 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_141 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_184 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_141 F I))).fv) 1)

noncomputable def nb077_alpha_dummy_185 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_144 x))).fv) 0)

noncomputable def nb077_alpha_dummy_186 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_144 x))).fv) 1)

noncomputable def nb077_alpha_dummy_187 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb077_alpha_dummy_188 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb077_alpha_dummy_189 (F : Class) (I : Class) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))))).fv) 0)

noncomputable def nb077_alpha_dummy_190 (x : Var) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))))).fv) 0)

noncomputable def nb077_alpha_dummy_191 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_184 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_192 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_184 F I))).fv) 1)

noncomputable def nb077_alpha_dummy_193 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_186 x))).fv) 0)

noncomputable def nb077_alpha_dummy_194 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_186 x))).fv) 1)

noncomputable def nb077_alpha_dummy_195 (F : Class) (I : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_191 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_191 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_191 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_196 (x : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_193 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_193 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_193 x))).fv) 0)

noncomputable def nb077_alpha_dummy_197 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb077_alpha_dummy_198 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb077_alpha_dummy_199 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb077_alpha_dummy_200 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb077_alpha_dummy_201 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb077_alpha_dummy_202 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb077_alpha_dummy_203 (F : Class) (I : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_198 F I)) (Class.cv (nb077_alpha_dummy_199 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_198 F I)) (Class.cv (nb077_alpha_dummy_199 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_204 (x : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_201 x)) (Class.cv (nb077_alpha_dummy_202 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_201 x)) (Class.cv (nb077_alpha_dummy_202 x)))).fv) 0)

noncomputable def nb077_alpha_dummy_205 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_198 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_199 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_206 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_201 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_202 x))).fv) 0)

noncomputable def nb077_alpha_dummy_207 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_198 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_199 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_208 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_201 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_202 x)))).fv) 0)

noncomputable def nb077_alpha_dummy_209 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_198 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_198 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_210 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_201 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_201 x))).fv) 0)

noncomputable def nb077_alpha_dummy_211 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_199 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_199 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_212 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_202 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_202 x))).fv) 0)

noncomputable def nb077_alpha_dummy_213 (F : Class) (I : Class) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb077_alpha_dummy_214 (x : Var) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb077_alpha_dummy_215 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb077_alpha_dummy_216 (x : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb077_alpha_dummy_217 (F : Class) (I : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_218 (x : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))).fv) 0)

noncomputable def nb077_alpha_dummy_219 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_141 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_140 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_220 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_141 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_140 F I))).fv) 1)

noncomputable def nb077_alpha_dummy_221 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_144 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) 0)

noncomputable def nb077_alpha_dummy_222 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_144 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) 1)

noncomputable def nb077_alpha_dummy_223 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb077_alpha_dummy_224 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb077_alpha_dummy_225 (F : Class) (I : Class) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))))).fv) 0)

noncomputable def nb077_alpha_dummy_226 (x : Var) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))))).fv) 0)

noncomputable def nb077_alpha_dummy_227 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_220 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_228 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_220 F I))).fv) 1)

noncomputable def nb077_alpha_dummy_229 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_222 x))).fv) 0)

noncomputable def nb077_alpha_dummy_230 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_222 x))).fv) 1)

noncomputable def nb077_alpha_dummy_231 (F : Class) (I : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_227 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_227 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_227 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_232 (x : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_229 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_229 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_229 x))).fv) 0)

noncomputable def nb077_alpha_dummy_233 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb077_alpha_dummy_234 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb077_alpha_dummy_235 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb077_alpha_dummy_236 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb077_alpha_dummy_237 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb077_alpha_dummy_238 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb077_alpha_dummy_239 (F : Class) (I : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_234 F I)) (Class.cv (nb077_alpha_dummy_235 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_234 F I)) (Class.cv (nb077_alpha_dummy_235 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_240 (x : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_237 x)) (Class.cv (nb077_alpha_dummy_238 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_237 x)) (Class.cv (nb077_alpha_dummy_238 x)))).fv) 0)

noncomputable def nb077_alpha_dummy_241 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_234 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_235 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_242 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_237 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_238 x))).fv) 0)

noncomputable def nb077_alpha_dummy_243 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_234 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_235 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_244 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_237 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_238 x)))).fv) 0)

noncomputable def nb077_alpha_dummy_245 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_234 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_234 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_246 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_237 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_237 x))).fv) 0)

noncomputable def nb077_alpha_dummy_247 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_235 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_235 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_248 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_238 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_238 x))).fv) 0)

noncomputable def nb077_alpha_dummy_249 (F : Class) (I : Class) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb077_alpha_dummy_250 (x : Var) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb077_alpha_dummy_251 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb077_alpha_dummy_252 (x : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb077_alpha_dummy_253 (F : Class) (I : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_254 (x : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))).fv) 0)

noncomputable def nb077_alpha_dummy_255 (F : Class) (I : Class) : Var := (freshVar (({(nb077_alpha_dummy_000 F I)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))).fv) 0)

noncomputable def nb077_alpha_dummy_256 (x : Var) : Var := (freshVar (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cplc (Class.cv x) (syn_c1c))).fv) 0)

noncomputable def nb077_alpha_dummy_257 (F : Class) (I : Class) : Var := (freshVar (({(nb077_alpha_dummy_000 F I)} : Finset Var) ∪ ({(nb077_alpha_dummy_255 F I)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb077_alpha_dummy_000 F I)) (syn_cvv)) (Wff.classEq (Class.cv (nb077_alpha_dummy_255 F I)) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))))).fv) 0)

noncomputable def nb077_alpha_dummy_258 (x : Var) : Var := (freshVar (({x} : Finset Var) ∪ ({(nb077_alpha_dummy_256 x)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classEq (Class.cv (nb077_alpha_dummy_256 x)) (syn_cplc (Class.cv x) (syn_c1c))))).fv) 0)

noncomputable def nb077_alpha_dummy_259 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_255 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_260 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_255 F I))).fv) 1)

noncomputable def nb077_alpha_dummy_261 (x : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb077_alpha_dummy_256 x))).fv) 0)

noncomputable def nb077_alpha_dummy_262 (x : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb077_alpha_dummy_256 x))).fv) 1)

noncomputable def nb077_alpha_dummy_263 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb077_alpha_dummy_264 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb077_alpha_dummy_265 (F : Class) (I : Class) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))))).fv) 0)

noncomputable def nb077_alpha_dummy_266 (x : Var) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))))).fv) 0)

noncomputable def nb077_alpha_dummy_267 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_260 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_268 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_260 F I))).fv) 1)

noncomputable def nb077_alpha_dummy_269 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_262 x))).fv) 0)

noncomputable def nb077_alpha_dummy_270 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_262 x))).fv) 1)

noncomputable def nb077_alpha_dummy_271 (F : Class) (I : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_267 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_267 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_267 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_272 (x : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_269 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_269 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_269 x))).fv) 0)

noncomputable def nb077_alpha_dummy_273 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb077_alpha_dummy_274 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb077_alpha_dummy_275 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb077_alpha_dummy_276 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb077_alpha_dummy_277 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb077_alpha_dummy_278 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb077_alpha_dummy_279 (F : Class) (I : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_274 F I)) (Class.cv (nb077_alpha_dummy_275 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_274 F I)) (Class.cv (nb077_alpha_dummy_275 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_280 (x : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_277 x)) (Class.cv (nb077_alpha_dummy_278 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_277 x)) (Class.cv (nb077_alpha_dummy_278 x)))).fv) 0)

noncomputable def nb077_alpha_dummy_281 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_274 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_275 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_282 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_277 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_278 x))).fv) 0)

noncomputable def nb077_alpha_dummy_283 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_274 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_275 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_284 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_277 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_278 x)))).fv) 0)

noncomputable def nb077_alpha_dummy_285 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_274 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_274 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_286 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_277 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_277 x))).fv) 0)

noncomputable def nb077_alpha_dummy_287 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_275 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_275 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_288 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_278 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_278 x))).fv) 0)

noncomputable def nb077_alpha_dummy_289 (F : Class) (I : Class) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb077_alpha_dummy_290 (x : Var) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb077_alpha_dummy_291 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb077_alpha_dummy_292 (x : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb077_alpha_dummy_293 (F : Class) (I : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_294 (x : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))).fv) 0)

noncomputable def nb077_alpha_dummy_295 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb077_alpha_dummy_296 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb077_alpha_dummy_297 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb077_alpha_dummy_298 (x : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb077_alpha_dummy_299 (x : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((syn_c1c)).fv) 1)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
