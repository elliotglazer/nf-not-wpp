import NAR4C056C001Part001

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

noncomputable def nb056_alpha_dummy_150 (f : Var) : Var := (freshVar (((Class.cv (nb056_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_146 f))).fv) 0)

noncomputable def nb056_alpha_dummy_151 : Var := (freshVar (((syn_ccompl (Class.cv (nb056_alpha_dummy_142)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_143)))).fv) 0)

noncomputable def nb056_alpha_dummy_152 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb056_alpha_dummy_145 f)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_146 f)))).fv) 0)

noncomputable def nb056_alpha_dummy_153 : Var := (freshVar (((Class.cv (nb056_alpha_dummy_142))).fv ∪ ((Class.cv (nb056_alpha_dummy_142))).fv) 0)

noncomputable def nb056_alpha_dummy_154 (f : Var) : Var := (freshVar (((Class.cv (nb056_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_145 f))).fv) 0)

noncomputable def nb056_alpha_dummy_155 : Var := (freshVar (((Class.cv (nb056_alpha_dummy_143))).fv ∪ ((Class.cv (nb056_alpha_dummy_143))).fv) 0)

noncomputable def nb056_alpha_dummy_156 (f : Var) : Var := (freshVar (((Class.cv (nb056_alpha_dummy_146 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_146 f))).fv) 0)

noncomputable def nb056_alpha_dummy_157 : Var := (freshVar (((Class.cab (nb056_alpha_dummy_127) (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085)) (Wff.classEq (Class.cv (nb056_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_127) (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085)) (Wff.classEq (Class.cv (nb056_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb056_alpha_dummy_158 (f : Var) : Var := (freshVar (((Class.cab (nb056_alpha_dummy_129 f) (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_129 f) (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb056_alpha_dummy_159 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_128))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb056_alpha_dummy_160 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb056_alpha_dummy_161 : Var := (freshVar (((syn_cphi (Class.cv (nb056_alpha_dummy_128)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_128)))).fv) 0)

noncomputable def nb056_alpha_dummy_162 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))).fv) 0)

noncomputable def nb056_alpha_dummy_163 : Var := (freshVar (((Class.cv (nb056_alpha_dummy_007))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) 0)

noncomputable def nb056_alpha_dummy_164 : Var := (freshVar (((Class.cv (nb056_alpha_dummy_007))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) 1)

noncomputable def nb056_alpha_dummy_165 (f : Var) : Var := (freshVar (((Class.cv (nb056_alpha_dummy_010 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) 0)

noncomputable def nb056_alpha_dummy_166 (f : Var) : Var := (freshVar (((Class.cv (nb056_alpha_dummy_010 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) 1)

noncomputable def nb056_alpha_dummy_167 : Var := (freshVar (((syn_ccompl (Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cphi (Class.cv (nb056_alpha_dummy_164)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb056_alpha_dummy_168 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb056_alpha_dummy_169 : Var := (freshVar (((Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cphi (Class.cv (nb056_alpha_dummy_164))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cphi (Class.cv (nb056_alpha_dummy_164))))))).fv) 0)

noncomputable def nb056_alpha_dummy_170 (f : Var) : Var := (freshVar (((Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))))))).fv) 0)

noncomputable def nb056_alpha_dummy_171 : Var := (freshVar (((Class.cv (nb056_alpha_dummy_164))).fv) 0)

noncomputable def nb056_alpha_dummy_172 : Var := (freshVar (((Class.cv (nb056_alpha_dummy_164))).fv) 1)

noncomputable def nb056_alpha_dummy_173 (f : Var) : Var := (freshVar (((Class.cv (nb056_alpha_dummy_166 f))).fv) 0)

noncomputable def nb056_alpha_dummy_174 (f : Var) : Var := (freshVar (((Class.cv (nb056_alpha_dummy_166 f))).fv) 1)

noncomputable def nb056_alpha_dummy_175 : Var := (freshVar (((Wff.classMem (Class.cv (nb056_alpha_dummy_171)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_171)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_171))).fv) 0)

noncomputable def nb056_alpha_dummy_176 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb056_alpha_dummy_173 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_173 f)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_173 f))).fv) 0)

noncomputable def nb056_alpha_dummy_177 : Var := (freshVar (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb056_alpha_dummy_178 : Var := (freshVar (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb056_alpha_dummy_179 : Var := (freshVar (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb056_alpha_dummy_180 (f : Var) : Var := (freshVar (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb056_alpha_dummy_181 (f : Var) : Var := (freshVar (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb056_alpha_dummy_182 (f : Var) : Var := (freshVar (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb056_alpha_dummy_183 : Var := (freshVar (((syn_cnin (Class.cv (nb056_alpha_dummy_178)) (Class.cv (nb056_alpha_dummy_179)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_178)) (Class.cv (nb056_alpha_dummy_179)))).fv) 0)

noncomputable def nb056_alpha_dummy_184 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb056_alpha_dummy_181 f)) (Class.cv (nb056_alpha_dummy_182 f)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_181 f)) (Class.cv (nb056_alpha_dummy_182 f)))).fv) 0)

noncomputable def nb056_alpha_dummy_185 : Var := (freshVar (((Class.cv (nb056_alpha_dummy_178))).fv ∪ ((Class.cv (nb056_alpha_dummy_179))).fv) 0)

noncomputable def nb056_alpha_dummy_186 (f : Var) : Var := (freshVar (((Class.cv (nb056_alpha_dummy_181 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_182 f))).fv) 0)

noncomputable def nb056_alpha_dummy_187 : Var := (freshVar (((syn_ccompl (Class.cv (nb056_alpha_dummy_178)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_179)))).fv) 0)

noncomputable def nb056_alpha_dummy_188 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb056_alpha_dummy_181 f)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_182 f)))).fv) 0)

noncomputable def nb056_alpha_dummy_189 : Var := (freshVar (((Class.cv (nb056_alpha_dummy_178))).fv ∪ ((Class.cv (nb056_alpha_dummy_178))).fv) 0)

noncomputable def nb056_alpha_dummy_190 (f : Var) : Var := (freshVar (((Class.cv (nb056_alpha_dummy_181 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_181 f))).fv) 0)

noncomputable def nb056_alpha_dummy_191 : Var := (freshVar (((Class.cv (nb056_alpha_dummy_179))).fv ∪ ((Class.cv (nb056_alpha_dummy_179))).fv) 0)

noncomputable def nb056_alpha_dummy_192 (f : Var) : Var := (freshVar (((Class.cv (nb056_alpha_dummy_182 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_182 f))).fv) 0)

noncomputable def nb056_alpha_dummy_193 : Var := (freshVar (((Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb056_alpha_dummy_194 (f : Var) : Var := (freshVar (((Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb056_alpha_dummy_195 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_164))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb056_alpha_dummy_196 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb056_alpha_dummy_197 : Var := (freshVar (((syn_cphi (Class.cv (nb056_alpha_dummy_164)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_164)))).fv) 0)

noncomputable def nb056_alpha_dummy_198 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))).fv) 0)

theorem nb056_fresh_000 : (nb056_alpha_dummy_019) ∉ (((Class.cab (nb056_alpha_dummy_013) (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_005)) (Wff.classEq (Class.cv (nb056_alpha_dummy_013)) (syn_cphi (Class.cv (nb056_alpha_dummy_014))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_013) (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_005)) (Wff.classEq (Class.cv (nb056_alpha_dummy_013)) (syn_cphi (Class.cv (nb056_alpha_dummy_014))))))).fv) := by
  simpa only [nb056_alpha_dummy_019] using freshVar_not_mem (((Class.cab (nb056_alpha_dummy_013) (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_005)) (Wff.classEq (Class.cv (nb056_alpha_dummy_013)) (syn_cphi (Class.cv (nb056_alpha_dummy_014))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_013) (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_005)) (Wff.classEq (Class.cv (nb056_alpha_dummy_013)) (syn_cphi (Class.cv (nb056_alpha_dummy_014))))))).fv) 0

theorem nb056_fresh_001 : (nb056_alpha_dummy_043) ∉ (((Class.cab (nb056_alpha_dummy_013) (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_013)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_013) (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_013)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb056_alpha_dummy_043] using freshVar_not_mem (((Class.cab (nb056_alpha_dummy_013) (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_013)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_013) (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_013)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb056_fresh_002 (f : Var) : (nb056_alpha_dummy_020 f) ∉ (((Class.cab (nb056_alpha_dummy_015 f) (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_008 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_015 f) (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_008 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))))))).fv) := by
  simpa only [nb056_alpha_dummy_020] using freshVar_not_mem (((Class.cab (nb056_alpha_dummy_015 f) (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_008 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_015 f) (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_008 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))))))).fv) 0

theorem nb056_fresh_003 (f : Var) : (nb056_alpha_dummy_044 f) ∉ (((Class.cab (nb056_alpha_dummy_015 f) (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_015 f) (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb056_alpha_dummy_044] using freshVar_not_mem (((Class.cab (nb056_alpha_dummy_015 f) (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_015 f) (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb056_fresh_004 : (nb056_alpha_dummy_055) ∉ (((Class.cab (nb056_alpha_dummy_049) (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_005)) (Wff.classEq (Class.cv (nb056_alpha_dummy_049)) (syn_cphi (Class.cv (nb056_alpha_dummy_050))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_049) (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_005)) (Wff.classEq (Class.cv (nb056_alpha_dummy_049)) (syn_cphi (Class.cv (nb056_alpha_dummy_050))))))).fv) := by
  simpa only [nb056_alpha_dummy_055] using freshVar_not_mem (((Class.cab (nb056_alpha_dummy_049) (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_005)) (Wff.classEq (Class.cv (nb056_alpha_dummy_049)) (syn_cphi (Class.cv (nb056_alpha_dummy_050))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_049) (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_005)) (Wff.classEq (Class.cv (nb056_alpha_dummy_049)) (syn_cphi (Class.cv (nb056_alpha_dummy_050))))))).fv) 0

theorem nb056_fresh_005 : (nb056_alpha_dummy_079) ∉ (((Class.cab (nb056_alpha_dummy_049) (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_049)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_049) (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_049)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb056_alpha_dummy_079] using freshVar_not_mem (((Class.cab (nb056_alpha_dummy_049) (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_049)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_049) (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_049)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb056_fresh_006 (f : Var) : (nb056_alpha_dummy_056 f) ∉ (((Class.cab (nb056_alpha_dummy_051 f) (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_008 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_051 f) (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_008 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))))))).fv) := by
  simpa only [nb056_alpha_dummy_056] using freshVar_not_mem (((Class.cab (nb056_alpha_dummy_051 f) (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_008 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_051 f) (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_008 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))))))).fv) 0

theorem nb056_fresh_007 (f : Var) : (nb056_alpha_dummy_080 f) ∉ (((Class.cab (nb056_alpha_dummy_051 f) (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_051 f) (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb056_alpha_dummy_080] using freshVar_not_mem (((Class.cab (nb056_alpha_dummy_051 f) (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_051 f) (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb056_fresh_008 : (nb056_alpha_dummy_097) ∉ (((Class.cab (nb056_alpha_dummy_091) (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_085)) (Wff.classEq (Class.cv (nb056_alpha_dummy_091)) (syn_cphi (Class.cv (nb056_alpha_dummy_092))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_091) (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_085)) (Wff.classEq (Class.cv (nb056_alpha_dummy_091)) (syn_cphi (Class.cv (nb056_alpha_dummy_092))))))).fv) := by
  simpa only [nb056_alpha_dummy_097] using freshVar_not_mem (((Class.cab (nb056_alpha_dummy_091) (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_085)) (Wff.classEq (Class.cv (nb056_alpha_dummy_091)) (syn_cphi (Class.cv (nb056_alpha_dummy_092))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_091) (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_085)) (Wff.classEq (Class.cv (nb056_alpha_dummy_091)) (syn_cphi (Class.cv (nb056_alpha_dummy_092))))))).fv) 0

theorem nb056_fresh_009 : (nb056_alpha_dummy_121) ∉ (((Class.cab (nb056_alpha_dummy_091) (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086)) (Wff.classEq (Class.cv (nb056_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_091) (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086)) (Wff.classEq (Class.cv (nb056_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb056_alpha_dummy_121] using freshVar_not_mem (((Class.cab (nb056_alpha_dummy_091) (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086)) (Wff.classEq (Class.cv (nb056_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_091) (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086)) (Wff.classEq (Class.cv (nb056_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb056_fresh_010 (f : Var) : (nb056_alpha_dummy_098 f) ∉ (((Class.cab (nb056_alpha_dummy_093 f) (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_093 f) (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))))))).fv) := by
  simpa only [nb056_alpha_dummy_098] using freshVar_not_mem (((Class.cab (nb056_alpha_dummy_093 f) (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_093 f) (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))))))).fv) 0

theorem nb056_fresh_011 (f : Var) : (nb056_alpha_dummy_122 f) ∉ (((Class.cab (nb056_alpha_dummy_093 f) (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_093 f) (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb056_alpha_dummy_122] using freshVar_not_mem (((Class.cab (nb056_alpha_dummy_093 f) (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_093 f) (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb056_fresh_012 : (nb056_alpha_dummy_157) ∉ (((Class.cab (nb056_alpha_dummy_127) (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085)) (Wff.classEq (Class.cv (nb056_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_127) (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085)) (Wff.classEq (Class.cv (nb056_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb056_alpha_dummy_157] using freshVar_not_mem (((Class.cab (nb056_alpha_dummy_127) (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085)) (Wff.classEq (Class.cv (nb056_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_127) (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085)) (Wff.classEq (Class.cv (nb056_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb056_fresh_013 : (nb056_alpha_dummy_133) ∉ (((Class.cab (nb056_alpha_dummy_127) (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_086)) (Wff.classEq (Class.cv (nb056_alpha_dummy_127)) (syn_cphi (Class.cv (nb056_alpha_dummy_128))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_127) (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_086)) (Wff.classEq (Class.cv (nb056_alpha_dummy_127)) (syn_cphi (Class.cv (nb056_alpha_dummy_128))))))).fv) := by
  simpa only [nb056_alpha_dummy_133] using freshVar_not_mem (((Class.cab (nb056_alpha_dummy_127) (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_086)) (Wff.classEq (Class.cv (nb056_alpha_dummy_127)) (syn_cphi (Class.cv (nb056_alpha_dummy_128))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_127) (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_086)) (Wff.classEq (Class.cv (nb056_alpha_dummy_127)) (syn_cphi (Class.cv (nb056_alpha_dummy_128))))))).fv) 0

theorem nb056_fresh_014 (f : Var) : (nb056_alpha_dummy_158 f) ∉ (((Class.cab (nb056_alpha_dummy_129 f) (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_129 f) (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb056_alpha_dummy_158] using freshVar_not_mem (((Class.cab (nb056_alpha_dummy_129 f) (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_129 f) (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb056_fresh_015 (f : Var) : (nb056_alpha_dummy_134 f) ∉ (((Class.cab (nb056_alpha_dummy_129 f) (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_129 f) (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))))))).fv) := by
  simpa only [nb056_alpha_dummy_134] using freshVar_not_mem (((Class.cab (nb056_alpha_dummy_129 f) (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_129 f) (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))))))).fv) 0

theorem nb056_fresh_016 : (nb056_alpha_dummy_193) ∉ (((Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb056_alpha_dummy_193] using freshVar_not_mem (((Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb056_fresh_017 : (nb056_alpha_dummy_169) ∉ (((Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cphi (Class.cv (nb056_alpha_dummy_164))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cphi (Class.cv (nb056_alpha_dummy_164))))))).fv) := by
  simpa only [nb056_alpha_dummy_169] using freshVar_not_mem (((Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cphi (Class.cv (nb056_alpha_dummy_164))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cphi (Class.cv (nb056_alpha_dummy_164))))))).fv) 0

theorem nb056_fresh_018 (f : Var) : (nb056_alpha_dummy_194 f) ∉ (((Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb056_alpha_dummy_194] using freshVar_not_mem (((Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb056_fresh_019 (f : Var) : (nb056_alpha_dummy_170 f) ∉ (((Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))))))).fv) := by
  simpa only [nb056_alpha_dummy_170] using freshVar_not_mem (((Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))))))).fv) 0

theorem nb056_fresh_020 : (nb056_alpha_dummy_085) ∉ (((Class.cv (nb056_alpha_dummy_000))).fv) := by
  simpa only [nb056_alpha_dummy_085] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_000))).fv) 0

theorem nb056_fresh_021 : (nb056_alpha_dummy_086) ∉ (((Class.cv (nb056_alpha_dummy_000))).fv) := by
  simpa only [nb056_alpha_dummy_086] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_000))).fv) 1

theorem nb056_distinct_022 : (nb056_alpha_dummy_085) ≠ (nb056_alpha_dummy_086) := by
  simpa only [nb056_alpha_dummy_085, nb056_alpha_dummy_086] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_000))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_023 : (nb056_alpha_dummy_005) ∉ (((Class.cv (nb056_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv) := by
  simpa only [nb056_alpha_dummy_005] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv) 0

theorem nb056_fresh_024 : (nb056_alpha_dummy_006) ∉ (((Class.cv (nb056_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv) := by
  simpa only [nb056_alpha_dummy_006] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv) 1

theorem nb056_fresh_025 : (nb056_alpha_dummy_007) ∉ (((Class.cv (nb056_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv) := by
  simpa only [nb056_alpha_dummy_007] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv) 2

theorem nb056_distinct_026 : (nb056_alpha_dummy_005) ≠ (nb056_alpha_dummy_006) := by
  simpa only [nb056_alpha_dummy_005, nb056_alpha_dummy_006] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_distinct_027 : (nb056_alpha_dummy_005) ≠ (nb056_alpha_dummy_007) := by
  simpa only [nb056_alpha_dummy_005, nb056_alpha_dummy_007] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv) (i := 0) (j := 2) (by decide))

theorem nb056_distinct_028 : (nb056_alpha_dummy_006) ≠ (nb056_alpha_dummy_007) := by
  simpa only [nb056_alpha_dummy_006, nb056_alpha_dummy_007] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv) (i := 1) (j := 2) (by decide))

theorem nb056_fresh_029 : (nb056_alpha_dummy_013) ∉ (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) := by
  simpa only [nb056_alpha_dummy_013] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) 0

theorem nb056_fresh_030 : (nb056_alpha_dummy_014) ∉ (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) := by
  simpa only [nb056_alpha_dummy_014] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) 1

theorem nb056_distinct_031 : (nb056_alpha_dummy_013) ≠ (nb056_alpha_dummy_014) := by
  simpa only [nb056_alpha_dummy_013, nb056_alpha_dummy_014] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_032 : (nb056_alpha_dummy_049) ∉ (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_007))).fv) := by
  simpa only [nb056_alpha_dummy_049] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_007))).fv) 0

theorem nb056_fresh_033 : (nb056_alpha_dummy_050) ∉ (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_007))).fv) := by
  simpa only [nb056_alpha_dummy_050] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_007))).fv) 1

theorem nb056_distinct_034 : (nb056_alpha_dummy_049) ≠ (nb056_alpha_dummy_050) := by
  simpa only [nb056_alpha_dummy_049, nb056_alpha_dummy_050] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_007))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_035 : (nb056_alpha_dummy_163) ∉ (((Class.cv (nb056_alpha_dummy_007))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) := by
  simpa only [nb056_alpha_dummy_163] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_007))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) 0

theorem nb056_fresh_036 : (nb056_alpha_dummy_164) ∉ (((Class.cv (nb056_alpha_dummy_007))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) := by
  simpa only [nb056_alpha_dummy_164] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_007))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) 1

theorem nb056_distinct_037 : (nb056_alpha_dummy_163) ≠ (nb056_alpha_dummy_164) := by
  simpa only [nb056_alpha_dummy_163, nb056_alpha_dummy_164] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_007))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_038 (f : Var) : (nb056_alpha_dummy_015 f) ∉ (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) := by
  simpa only [nb056_alpha_dummy_015] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) 0

theorem nb056_fresh_039 (f : Var) : (nb056_alpha_dummy_016 f) ∉ (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) := by
  simpa only [nb056_alpha_dummy_016] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) 1

theorem nb056_distinct_040 (f : Var) : (nb056_alpha_dummy_015 f) ≠ (nb056_alpha_dummy_016 f) := by
  simpa only [nb056_alpha_dummy_015, nb056_alpha_dummy_016] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_041 (f : Var) : (nb056_alpha_dummy_051 f) ∉ (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_010 f))).fv) := by
  simpa only [nb056_alpha_dummy_051] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_010 f))).fv) 0

theorem nb056_fresh_042 (f : Var) : (nb056_alpha_dummy_052 f) ∉ (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_010 f))).fv) := by
  simpa only [nb056_alpha_dummy_052] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_010 f))).fv) 1

theorem nb056_distinct_043 (f : Var) : (nb056_alpha_dummy_051 f) ≠ (nb056_alpha_dummy_052 f) := by
  simpa only [nb056_alpha_dummy_051, nb056_alpha_dummy_052] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_010 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_044 (f : Var) : (nb056_alpha_dummy_165 f) ∉ (((Class.cv (nb056_alpha_dummy_010 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) := by
  simpa only [nb056_alpha_dummy_165] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_010 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) 0

theorem nb056_fresh_045 (f : Var) : (nb056_alpha_dummy_166 f) ∉ (((Class.cv (nb056_alpha_dummy_010 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) := by
  simpa only [nb056_alpha_dummy_166] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_010 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) 1

theorem nb056_distinct_046 (f : Var) : (nb056_alpha_dummy_165 f) ≠ (nb056_alpha_dummy_166 f) := by
  simpa only [nb056_alpha_dummy_165, nb056_alpha_dummy_166] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_010 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_047 : (nb056_alpha_dummy_021) ∉ (((Class.cv (nb056_alpha_dummy_014))).fv) := by
  simpa only [nb056_alpha_dummy_021] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_014))).fv) 0

theorem nb056_fresh_048 : (nb056_alpha_dummy_022) ∉ (((Class.cv (nb056_alpha_dummy_014))).fv) := by
  simpa only [nb056_alpha_dummy_022] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_014))).fv) 1

theorem nb056_distinct_049 : (nb056_alpha_dummy_021) ≠ (nb056_alpha_dummy_022) := by
  simpa only [nb056_alpha_dummy_021, nb056_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_014))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_050 (f : Var) : (nb056_alpha_dummy_023 f) ∉ (((Class.cv (nb056_alpha_dummy_016 f))).fv) := by
  simpa only [nb056_alpha_dummy_023] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_016 f))).fv) 0

theorem nb056_fresh_051 (f : Var) : (nb056_alpha_dummy_024 f) ∉ (((Class.cv (nb056_alpha_dummy_016 f))).fv) := by
  simpa only [nb056_alpha_dummy_024] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_016 f))).fv) 1

theorem nb056_distinct_052 (f : Var) : (nb056_alpha_dummy_023 f) ≠ (nb056_alpha_dummy_024 f) := by
  simpa only [nb056_alpha_dummy_023, nb056_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_016 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_053 : (nb056_alpha_dummy_027) ∉ (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_027] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) 0

theorem nb056_fresh_054 : (nb056_alpha_dummy_028) ∉ (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_028] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) 1

theorem nb056_fresh_055 : (nb056_alpha_dummy_029) ∉ (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_029] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) 2

theorem nb056_distinct_056 : (nb056_alpha_dummy_027) ≠ (nb056_alpha_dummy_028) := by
  simpa only [nb056_alpha_dummy_027, nb056_alpha_dummy_028] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb056_distinct_057 : (nb056_alpha_dummy_027) ≠ (nb056_alpha_dummy_029) := by
  simpa only [nb056_alpha_dummy_027, nb056_alpha_dummy_029] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb056_distinct_058 : (nb056_alpha_dummy_028) ≠ (nb056_alpha_dummy_029) := by
  simpa only [nb056_alpha_dummy_028, nb056_alpha_dummy_029] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb056_fresh_059 (f : Var) : (nb056_alpha_dummy_030 f) ∉ (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_030] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb056_fresh_060 (f : Var) : (nb056_alpha_dummy_031 f) ∉ (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_031] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb056_fresh_061 (f : Var) : (nb056_alpha_dummy_032 f) ∉ (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_032] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb056_distinct_062 (f : Var) : (nb056_alpha_dummy_030 f) ≠ (nb056_alpha_dummy_031 f) := by
  simpa only [nb056_alpha_dummy_030, nb056_alpha_dummy_031] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb056_distinct_063 (f : Var) : (nb056_alpha_dummy_030 f) ≠ (nb056_alpha_dummy_032 f) := by
  simpa only [nb056_alpha_dummy_030, nb056_alpha_dummy_032] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb056_distinct_064 (f : Var) : (nb056_alpha_dummy_031 f) ≠ (nb056_alpha_dummy_032 f) := by
  simpa only [nb056_alpha_dummy_031, nb056_alpha_dummy_032] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb056_fresh_065 : (nb056_alpha_dummy_039) ∉ (((Class.cv (nb056_alpha_dummy_028))).fv ∪ ((Class.cv (nb056_alpha_dummy_028))).fv) := by
  simpa only [nb056_alpha_dummy_039] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_028))).fv ∪ ((Class.cv (nb056_alpha_dummy_028))).fv) 0

theorem nb056_fresh_066 : (nb056_alpha_dummy_035) ∉ (((Class.cv (nb056_alpha_dummy_028))).fv ∪ ((Class.cv (nb056_alpha_dummy_029))).fv) := by
  simpa only [nb056_alpha_dummy_035] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_028))).fv ∪ ((Class.cv (nb056_alpha_dummy_029))).fv) 0

theorem nb056_fresh_067 : (nb056_alpha_dummy_041) ∉ (((Class.cv (nb056_alpha_dummy_029))).fv ∪ ((Class.cv (nb056_alpha_dummy_029))).fv) := by
  simpa only [nb056_alpha_dummy_041] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_029))).fv ∪ ((Class.cv (nb056_alpha_dummy_029))).fv) 0

theorem nb056_fresh_068 (f : Var) : (nb056_alpha_dummy_040 f) ∉ (((Class.cv (nb056_alpha_dummy_031 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_031 f))).fv) := by
  simpa only [nb056_alpha_dummy_040] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_031 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_031 f))).fv) 0

theorem nb056_fresh_069 (f : Var) : (nb056_alpha_dummy_036 f) ∉ (((Class.cv (nb056_alpha_dummy_031 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_032 f))).fv) := by
  simpa only [nb056_alpha_dummy_036] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_031 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_032 f))).fv) 0

theorem nb056_fresh_070 (f : Var) : (nb056_alpha_dummy_042 f) ∉ (((Class.cv (nb056_alpha_dummy_032 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_032 f))).fv) := by
  simpa only [nb056_alpha_dummy_042] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_032 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_032 f))).fv) 0

theorem nb056_fresh_071 : (nb056_alpha_dummy_057) ∉ (((Class.cv (nb056_alpha_dummy_050))).fv) := by
  simpa only [nb056_alpha_dummy_057] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_050))).fv) 0

theorem nb056_fresh_072 : (nb056_alpha_dummy_058) ∉ (((Class.cv (nb056_alpha_dummy_050))).fv) := by
  simpa only [nb056_alpha_dummy_058] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_050))).fv) 1

theorem nb056_distinct_073 : (nb056_alpha_dummy_057) ≠ (nb056_alpha_dummy_058) := by
  simpa only [nb056_alpha_dummy_057, nb056_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_050))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_074 (f : Var) : (nb056_alpha_dummy_059 f) ∉ (((Class.cv (nb056_alpha_dummy_052 f))).fv) := by
  simpa only [nb056_alpha_dummy_059] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_052 f))).fv) 0

theorem nb056_fresh_075 (f : Var) : (nb056_alpha_dummy_060 f) ∉ (((Class.cv (nb056_alpha_dummy_052 f))).fv) := by
  simpa only [nb056_alpha_dummy_060] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_052 f))).fv) 1

theorem nb056_distinct_076 (f : Var) : (nb056_alpha_dummy_059 f) ≠ (nb056_alpha_dummy_060 f) := by
  simpa only [nb056_alpha_dummy_059, nb056_alpha_dummy_060] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_052 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_077 : (nb056_alpha_dummy_063) ∉ (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_063] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) 0

theorem nb056_fresh_078 : (nb056_alpha_dummy_064) ∉ (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_064] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) 1

theorem nb056_fresh_079 : (nb056_alpha_dummy_065) ∉ (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_065] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) 2

theorem nb056_distinct_080 : (nb056_alpha_dummy_063) ≠ (nb056_alpha_dummy_064) := by
  simpa only [nb056_alpha_dummy_063, nb056_alpha_dummy_064] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb056_distinct_081 : (nb056_alpha_dummy_063) ≠ (nb056_alpha_dummy_065) := by
  simpa only [nb056_alpha_dummy_063, nb056_alpha_dummy_065] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb056_distinct_082 : (nb056_alpha_dummy_064) ≠ (nb056_alpha_dummy_065) := by
  simpa only [nb056_alpha_dummy_064, nb056_alpha_dummy_065] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb056_fresh_083 (f : Var) : (nb056_alpha_dummy_066 f) ∉ (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_066] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb056_fresh_084 (f : Var) : (nb056_alpha_dummy_067 f) ∉ (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_067] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb056_fresh_085 (f : Var) : (nb056_alpha_dummy_068 f) ∉ (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_068] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb056_distinct_086 (f : Var) : (nb056_alpha_dummy_066 f) ≠ (nb056_alpha_dummy_067 f) := by
  simpa only [nb056_alpha_dummy_066, nb056_alpha_dummy_067] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb056_distinct_087 (f : Var) : (nb056_alpha_dummy_066 f) ≠ (nb056_alpha_dummy_068 f) := by
  simpa only [nb056_alpha_dummy_066, nb056_alpha_dummy_068] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb056_distinct_088 (f : Var) : (nb056_alpha_dummy_067 f) ≠ (nb056_alpha_dummy_068 f) := by
  simpa only [nb056_alpha_dummy_067, nb056_alpha_dummy_068] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb056_fresh_089 : (nb056_alpha_dummy_075) ∉ (((Class.cv (nb056_alpha_dummy_064))).fv ∪ ((Class.cv (nb056_alpha_dummy_064))).fv) := by
  simpa only [nb056_alpha_dummy_075] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_064))).fv ∪ ((Class.cv (nb056_alpha_dummy_064))).fv) 0

theorem nb056_fresh_090 : (nb056_alpha_dummy_071) ∉ (((Class.cv (nb056_alpha_dummy_064))).fv ∪ ((Class.cv (nb056_alpha_dummy_065))).fv) := by
  simpa only [nb056_alpha_dummy_071] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_064))).fv ∪ ((Class.cv (nb056_alpha_dummy_065))).fv) 0

theorem nb056_fresh_091 : (nb056_alpha_dummy_077) ∉ (((Class.cv (nb056_alpha_dummy_065))).fv ∪ ((Class.cv (nb056_alpha_dummy_065))).fv) := by
  simpa only [nb056_alpha_dummy_077] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_065))).fv ∪ ((Class.cv (nb056_alpha_dummy_065))).fv) 0

theorem nb056_fresh_092 (f : Var) : (nb056_alpha_dummy_076 f) ∉ (((Class.cv (nb056_alpha_dummy_067 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_067 f))).fv) := by
  simpa only [nb056_alpha_dummy_076] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_067 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_067 f))).fv) 0

theorem nb056_fresh_093 (f : Var) : (nb056_alpha_dummy_072 f) ∉ (((Class.cv (nb056_alpha_dummy_067 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_068 f))).fv) := by
  simpa only [nb056_alpha_dummy_072] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_067 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_068 f))).fv) 0

theorem nb056_fresh_094 (f : Var) : (nb056_alpha_dummy_078 f) ∉ (((Class.cv (nb056_alpha_dummy_068 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_068 f))).fv) := by
  simpa only [nb056_alpha_dummy_078] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_068 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_068 f))).fv) 0

theorem nb056_fresh_095 : (nb056_alpha_dummy_091) ∉ (((Class.cv (nb056_alpha_dummy_085))).fv ∪ ((Class.cv (nb056_alpha_dummy_086))).fv) := by
  simpa only [nb056_alpha_dummy_091] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_085))).fv ∪ ((Class.cv (nb056_alpha_dummy_086))).fv) 0

theorem nb056_fresh_096 : (nb056_alpha_dummy_092) ∉ (((Class.cv (nb056_alpha_dummy_085))).fv ∪ ((Class.cv (nb056_alpha_dummy_086))).fv) := by
  simpa only [nb056_alpha_dummy_092] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_085))).fv ∪ ((Class.cv (nb056_alpha_dummy_086))).fv) 1

theorem nb056_distinct_097 : (nb056_alpha_dummy_091) ≠ (nb056_alpha_dummy_092) := by
  simpa only [nb056_alpha_dummy_091, nb056_alpha_dummy_092] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_085))).fv ∪ ((Class.cv (nb056_alpha_dummy_086))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_098 : (nb056_alpha_dummy_127) ∉ (((Class.cv (nb056_alpha_dummy_086))).fv ∪ ((Class.cv (nb056_alpha_dummy_085))).fv) := by
  simpa only [nb056_alpha_dummy_127] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_086))).fv ∪ ((Class.cv (nb056_alpha_dummy_085))).fv) 0

theorem nb056_fresh_099 : (nb056_alpha_dummy_128) ∉ (((Class.cv (nb056_alpha_dummy_086))).fv ∪ ((Class.cv (nb056_alpha_dummy_085))).fv) := by
  simpa only [nb056_alpha_dummy_128] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_086))).fv ∪ ((Class.cv (nb056_alpha_dummy_085))).fv) 1

theorem nb056_distinct_100 : (nb056_alpha_dummy_127) ≠ (nb056_alpha_dummy_128) := by
  simpa only [nb056_alpha_dummy_127, nb056_alpha_dummy_128] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_086))).fv ∪ ((Class.cv (nb056_alpha_dummy_085))).fv) (i := 0) (j := 1) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
