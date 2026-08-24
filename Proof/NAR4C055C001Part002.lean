import NAR4C055C001Part001

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

noncomputable def nb055_alpha_dummy_150 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_119))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb055_alpha_dummy_151 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb055_alpha_dummy_152 : Var := (freshVar (((syn_cphi (Class.cv (nb055_alpha_dummy_119)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_119)))).fv) 0)

noncomputable def nb055_alpha_dummy_153 (x : Var) (y : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))).fv) 0)

noncomputable def nb055_alpha_dummy_154 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_078))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) 0)

noncomputable def nb055_alpha_dummy_155 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_078))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) 1)

noncomputable def nb055_alpha_dummy_156 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_079 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_017 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_157 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_079 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_017 x y))).fv) 1)

noncomputable def nb055_alpha_dummy_158 : Var := (freshVar (((syn_ccompl (Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cphi (Class.cv (nb055_alpha_dummy_155)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb055_alpha_dummy_159 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb055_alpha_dummy_160 : Var := (freshVar (((Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cphi (Class.cv (nb055_alpha_dummy_155))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cphi (Class.cv (nb055_alpha_dummy_155))))))).fv) 0)

noncomputable def nb055_alpha_dummy_161 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))))))).fv) 0)

noncomputable def nb055_alpha_dummy_162 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_155))).fv) 0)

noncomputable def nb055_alpha_dummy_163 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_155))).fv) 1)

noncomputable def nb055_alpha_dummy_164 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_157 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_165 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_157 x y))).fv) 1)

noncomputable def nb055_alpha_dummy_166 : Var := (freshVar (((Wff.classMem (Class.cv (nb055_alpha_dummy_162)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_162)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_162))).fv) 0)

noncomputable def nb055_alpha_dummy_167 (x : Var) (y : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb055_alpha_dummy_164 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_164 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_164 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_168 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb055_alpha_dummy_169 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb055_alpha_dummy_170 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb055_alpha_dummy_171 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb055_alpha_dummy_172 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb055_alpha_dummy_173 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb055_alpha_dummy_174 : Var := (freshVar (((syn_cnin (Class.cv (nb055_alpha_dummy_169)) (Class.cv (nb055_alpha_dummy_170)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_169)) (Class.cv (nb055_alpha_dummy_170)))).fv) 0)

noncomputable def nb055_alpha_dummy_175 (x : Var) (y : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb055_alpha_dummy_172 x y)) (Class.cv (nb055_alpha_dummy_173 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_172 x y)) (Class.cv (nb055_alpha_dummy_173 x y)))).fv) 0)

noncomputable def nb055_alpha_dummy_176 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_169))).fv ∪ ((Class.cv (nb055_alpha_dummy_170))).fv) 0)

noncomputable def nb055_alpha_dummy_177 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_172 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_173 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_178 : Var := (freshVar (((syn_ccompl (Class.cv (nb055_alpha_dummy_169)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_170)))).fv) 0)

noncomputable def nb055_alpha_dummy_179 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb055_alpha_dummy_172 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_173 x y)))).fv) 0)

noncomputable def nb055_alpha_dummy_180 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_169))).fv ∪ ((Class.cv (nb055_alpha_dummy_169))).fv) 0)

noncomputable def nb055_alpha_dummy_181 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_172 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_172 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_182 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_170))).fv ∪ ((Class.cv (nb055_alpha_dummy_170))).fv) 0)

noncomputable def nb055_alpha_dummy_183 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_173 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_173 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_184 : Var := (freshVar (((Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb055_alpha_dummy_185 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb055_alpha_dummy_186 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_155))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb055_alpha_dummy_187 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb055_alpha_dummy_188 : Var := (freshVar (((syn_cphi (Class.cv (nb055_alpha_dummy_155)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_155)))).fv) 0)

noncomputable def nb055_alpha_dummy_189 (x : Var) (y : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))).fv) 0)

theorem nb055_fresh_000 : (nb055_alpha_dummy_072) ∉ (((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002)) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002)) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb055_alpha_dummy_072] using freshVar_not_mem (((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002)) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002)) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb055_fresh_001 : (nb055_alpha_dummy_012) ∉ (((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001))) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cphi (Class.cv (nb055_alpha_dummy_007))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001))) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cphi (Class.cv (nb055_alpha_dummy_007))))))).fv) := by
  simpa only [nb055_alpha_dummy_012] using freshVar_not_mem (((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001))) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cphi (Class.cv (nb055_alpha_dummy_007))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001))) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cphi (Class.cv (nb055_alpha_dummy_007))))))).fv) 0

theorem nb055_fresh_002 (x : Var) (y : Var) : (nb055_alpha_dummy_073 x y) ∉ (((Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb055_alpha_dummy_073] using freshVar_not_mem (((Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb055_fresh_003 (x : Var) (y : Var) : (nb055_alpha_dummy_013 x y) ∉ (((Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))))).fv) := by
  simpa only [nb055_alpha_dummy_013] using freshVar_not_mem (((Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))))).fv) 0

theorem nb055_fresh_004 : (nb055_alpha_dummy_020) ∉ (((Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cphi (Class.cv (nb055_alpha_dummy_015))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cphi (Class.cv (nb055_alpha_dummy_015))))))).fv) := by
  simpa only [nb055_alpha_dummy_020] using freshVar_not_mem (((Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cphi (Class.cv (nb055_alpha_dummy_015))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cphi (Class.cv (nb055_alpha_dummy_015))))))).fv) 0

theorem nb055_fresh_005 : (nb055_alpha_dummy_044) ∉ (((Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb055_alpha_dummy_044] using freshVar_not_mem (((Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb055_fresh_006 (x : Var) (y : Var) : (nb055_alpha_dummy_021 x y) ∉ (((Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))))))).fv) := by
  simpa only [nb055_alpha_dummy_021] using freshVar_not_mem (((Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))))))).fv) 0

theorem nb055_fresh_007 (x : Var) (y : Var) : (nb055_alpha_dummy_045 x y) ∉ (((Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb055_alpha_dummy_045] using freshVar_not_mem (((Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb055_fresh_008 : (nb055_alpha_dummy_088) ∉ (((Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cphi (Class.cv (nb055_alpha_dummy_083))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cphi (Class.cv (nb055_alpha_dummy_083))))))).fv) := by
  simpa only [nb055_alpha_dummy_088] using freshVar_not_mem (((Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cphi (Class.cv (nb055_alpha_dummy_083))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cphi (Class.cv (nb055_alpha_dummy_083))))))).fv) 0

theorem nb055_fresh_009 : (nb055_alpha_dummy_112) ∉ (((Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb055_alpha_dummy_112] using freshVar_not_mem (((Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb055_fresh_010 (x : Var) (y : Var) : (nb055_alpha_dummy_089 x y) ∉ (((Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))))))).fv) := by
  simpa only [nb055_alpha_dummy_089] using freshVar_not_mem (((Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))))))).fv) 0

theorem nb055_fresh_011 (x : Var) (y : Var) : (nb055_alpha_dummy_113 x y) ∉ (((Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb055_alpha_dummy_113] using freshVar_not_mem (((Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb055_fresh_012 : (nb055_alpha_dummy_124) ∉ (((Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cphi (Class.cv (nb055_alpha_dummy_119))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cphi (Class.cv (nb055_alpha_dummy_119))))))).fv) := by
  simpa only [nb055_alpha_dummy_124] using freshVar_not_mem (((Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cphi (Class.cv (nb055_alpha_dummy_119))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cphi (Class.cv (nb055_alpha_dummy_119))))))).fv) 0

theorem nb055_fresh_013 : (nb055_alpha_dummy_148) ∉ (((Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb055_alpha_dummy_148] using freshVar_not_mem (((Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb055_fresh_014 (x : Var) (y : Var) : (nb055_alpha_dummy_125 x y) ∉ (((Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))))))).fv) := by
  simpa only [nb055_alpha_dummy_125] using freshVar_not_mem (((Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))))))).fv) 0

theorem nb055_fresh_015 (x : Var) (y : Var) : (nb055_alpha_dummy_149 x y) ∉ (((Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb055_alpha_dummy_149] using freshVar_not_mem (((Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb055_fresh_016 : (nb055_alpha_dummy_184) ∉ (((Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb055_alpha_dummy_184] using freshVar_not_mem (((Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb055_fresh_017 : (nb055_alpha_dummy_160) ∉ (((Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cphi (Class.cv (nb055_alpha_dummy_155))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cphi (Class.cv (nb055_alpha_dummy_155))))))).fv) := by
  simpa only [nb055_alpha_dummy_160] using freshVar_not_mem (((Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cphi (Class.cv (nb055_alpha_dummy_155))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cphi (Class.cv (nb055_alpha_dummy_155))))))).fv) 0

theorem nb055_fresh_018 (x : Var) (y : Var) : (nb055_alpha_dummy_185 x y) ∉ (((Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb055_alpha_dummy_185] using freshVar_not_mem (((Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb055_fresh_019 (x : Var) (y : Var) : (nb055_alpha_dummy_161 x y) ∉ (((Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))))))).fv) := by
  simpa only [nb055_alpha_dummy_161] using freshVar_not_mem (((Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))))))).fv) 0

theorem nb055_fresh_020 : (nb055_alpha_dummy_014) ∉ (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) := by
  simpa only [nb055_alpha_dummy_014] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) 0

theorem nb055_fresh_021 : (nb055_alpha_dummy_015) ∉ (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) := by
  simpa only [nb055_alpha_dummy_015] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) 1

theorem nb055_fresh_022 : (nb055_alpha_dummy_078) ∉ (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) := by
  simpa only [nb055_alpha_dummy_078] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) 2

theorem nb055_distinct_023 : (nb055_alpha_dummy_014) ≠ (nb055_alpha_dummy_015) := by
  simpa only [nb055_alpha_dummy_014, nb055_alpha_dummy_015] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_distinct_024 : (nb055_alpha_dummy_014) ≠ (nb055_alpha_dummy_078) := by
  simpa only [nb055_alpha_dummy_014, nb055_alpha_dummy_078] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) (i := 0) (j := 2) (by decide))

theorem nb055_distinct_025 : (nb055_alpha_dummy_015) ≠ (nb055_alpha_dummy_078) := by
  simpa only [nb055_alpha_dummy_015, nb055_alpha_dummy_078] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) (i := 1) (j := 2) (by decide))

theorem nb055_fresh_026 : (nb055_alpha_dummy_050) ∉ (((Class.cv (nb055_alpha_dummy_007))).fv) := by
  simpa only [nb055_alpha_dummy_050] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_007))).fv) 0

theorem nb055_fresh_027 : (nb055_alpha_dummy_051) ∉ (((Class.cv (nb055_alpha_dummy_007))).fv) := by
  simpa only [nb055_alpha_dummy_051] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_007))).fv) 1

theorem nb055_distinct_028 : (nb055_alpha_dummy_050) ≠ (nb055_alpha_dummy_051) := by
  simpa only [nb055_alpha_dummy_050, nb055_alpha_dummy_051] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_007))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_029 (x : Var) (y : Var) : (nb055_alpha_dummy_052 x y) ∉ (((Class.cv (nb055_alpha_dummy_009 x y))).fv) := by
  simpa only [nb055_alpha_dummy_052] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_009 x y))).fv) 0

theorem nb055_fresh_030 (x : Var) (y : Var) : (nb055_alpha_dummy_053 x y) ∉ (((Class.cv (nb055_alpha_dummy_009 x y))).fv) := by
  simpa only [nb055_alpha_dummy_053] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_009 x y))).fv) 1

theorem nb055_distinct_031 (x : Var) (y : Var) : (nb055_alpha_dummy_052 x y) ≠ (nb055_alpha_dummy_053 x y) := by
  simpa only [nb055_alpha_dummy_052, nb055_alpha_dummy_053] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_009 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_032 : (nb055_alpha_dummy_082) ∉ (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) := by
  simpa only [nb055_alpha_dummy_082] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) 0

theorem nb055_fresh_033 : (nb055_alpha_dummy_083) ∉ (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) := by
  simpa only [nb055_alpha_dummy_083] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) 1

theorem nb055_distinct_034 : (nb055_alpha_dummy_082) ≠ (nb055_alpha_dummy_083) := by
  simpa only [nb055_alpha_dummy_082, nb055_alpha_dummy_083] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_035 : (nb055_alpha_dummy_118) ∉ (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_078))).fv) := by
  simpa only [nb055_alpha_dummy_118] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_078))).fv) 0

theorem nb055_fresh_036 : (nb055_alpha_dummy_119) ∉ (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_078))).fv) := by
  simpa only [nb055_alpha_dummy_119] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_078))).fv) 1

theorem nb055_distinct_037 : (nb055_alpha_dummy_118) ≠ (nb055_alpha_dummy_119) := by
  simpa only [nb055_alpha_dummy_118, nb055_alpha_dummy_119] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_078))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_038 : (nb055_alpha_dummy_022) ∉ (((Class.cv (nb055_alpha_dummy_015))).fv) := by
  simpa only [nb055_alpha_dummy_022] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_015))).fv) 0

theorem nb055_fresh_039 : (nb055_alpha_dummy_023) ∉ (((Class.cv (nb055_alpha_dummy_015))).fv) := by
  simpa only [nb055_alpha_dummy_023] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_015))).fv) 1

theorem nb055_distinct_040 : (nb055_alpha_dummy_022) ≠ (nb055_alpha_dummy_023) := by
  simpa only [nb055_alpha_dummy_022, nb055_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_015))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_041 (x : Var) (y : Var) : (nb055_alpha_dummy_084 x y) ∉ (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_017 x y))).fv) := by
  simpa only [nb055_alpha_dummy_084] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_017 x y))).fv) 0

theorem nb055_fresh_042 (x : Var) (y : Var) : (nb055_alpha_dummy_085 x y) ∉ (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_017 x y))).fv) := by
  simpa only [nb055_alpha_dummy_085] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_017 x y))).fv) 1

theorem nb055_distinct_043 (x : Var) (y : Var) : (nb055_alpha_dummy_084 x y) ≠ (nb055_alpha_dummy_085 x y) := by
  simpa only [nb055_alpha_dummy_084, nb055_alpha_dummy_085] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_017 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_044 (x : Var) (y : Var) : (nb055_alpha_dummy_120 x y) ∉ (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_079 x y))).fv) := by
  simpa only [nb055_alpha_dummy_120] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_079 x y))).fv) 0

theorem nb055_fresh_045 (x : Var) (y : Var) : (nb055_alpha_dummy_121 x y) ∉ (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_079 x y))).fv) := by
  simpa only [nb055_alpha_dummy_121] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_079 x y))).fv) 1

theorem nb055_distinct_046 (x : Var) (y : Var) : (nb055_alpha_dummy_120 x y) ≠ (nb055_alpha_dummy_121 x y) := by
  simpa only [nb055_alpha_dummy_120, nb055_alpha_dummy_121] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_079 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_047 (x : Var) (y : Var) : (nb055_alpha_dummy_024 x y) ∉ (((Class.cv (nb055_alpha_dummy_017 x y))).fv) := by
  simpa only [nb055_alpha_dummy_024] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_017 x y))).fv) 0

theorem nb055_fresh_048 (x : Var) (y : Var) : (nb055_alpha_dummy_025 x y) ∉ (((Class.cv (nb055_alpha_dummy_017 x y))).fv) := by
  simpa only [nb055_alpha_dummy_025] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_017 x y))).fv) 1

theorem nb055_distinct_049 (x : Var) (y : Var) : (nb055_alpha_dummy_024 x y) ≠ (nb055_alpha_dummy_025 x y) := by
  simpa only [nb055_alpha_dummy_024, nb055_alpha_dummy_025] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_017 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_050 : (nb055_alpha_dummy_028) ∉ (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_028] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 0

theorem nb055_fresh_051 : (nb055_alpha_dummy_029) ∉ (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_029] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 1

theorem nb055_fresh_052 : (nb055_alpha_dummy_030) ∉ (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_030] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 2

theorem nb055_distinct_053 : (nb055_alpha_dummy_028) ≠ (nb055_alpha_dummy_029) := by
  simpa only [nb055_alpha_dummy_028, nb055_alpha_dummy_029] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb055_distinct_054 : (nb055_alpha_dummy_028) ≠ (nb055_alpha_dummy_030) := by
  simpa only [nb055_alpha_dummy_028, nb055_alpha_dummy_030] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb055_distinct_055 : (nb055_alpha_dummy_029) ≠ (nb055_alpha_dummy_030) := by
  simpa only [nb055_alpha_dummy_029, nb055_alpha_dummy_030] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb055_fresh_056 (x : Var) (y : Var) : (nb055_alpha_dummy_031 x y) ∉ (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_031] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb055_fresh_057 (x : Var) (y : Var) : (nb055_alpha_dummy_032 x y) ∉ (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_032] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb055_fresh_058 (x : Var) (y : Var) : (nb055_alpha_dummy_033 x y) ∉ (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_033] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb055_distinct_059 (x : Var) (y : Var) : (nb055_alpha_dummy_031 x y) ≠ (nb055_alpha_dummy_032 x y) := by
  simpa only [nb055_alpha_dummy_031, nb055_alpha_dummy_032] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb055_distinct_060 (x : Var) (y : Var) : (nb055_alpha_dummy_031 x y) ≠ (nb055_alpha_dummy_033 x y) := by
  simpa only [nb055_alpha_dummy_031, nb055_alpha_dummy_033] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb055_distinct_061 (x : Var) (y : Var) : (nb055_alpha_dummy_032 x y) ≠ (nb055_alpha_dummy_033 x y) := by
  simpa only [nb055_alpha_dummy_032, nb055_alpha_dummy_033] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb055_fresh_062 : (nb055_alpha_dummy_040) ∉ (((Class.cv (nb055_alpha_dummy_029))).fv ∪ ((Class.cv (nb055_alpha_dummy_029))).fv) := by
  simpa only [nb055_alpha_dummy_040] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_029))).fv ∪ ((Class.cv (nb055_alpha_dummy_029))).fv) 0

theorem nb055_fresh_063 : (nb055_alpha_dummy_036) ∉ (((Class.cv (nb055_alpha_dummy_029))).fv ∪ ((Class.cv (nb055_alpha_dummy_030))).fv) := by
  simpa only [nb055_alpha_dummy_036] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_029))).fv ∪ ((Class.cv (nb055_alpha_dummy_030))).fv) 0

theorem nb055_fresh_064 : (nb055_alpha_dummy_042) ∉ (((Class.cv (nb055_alpha_dummy_030))).fv ∪ ((Class.cv (nb055_alpha_dummy_030))).fv) := by
  simpa only [nb055_alpha_dummy_042] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_030))).fv ∪ ((Class.cv (nb055_alpha_dummy_030))).fv) 0

theorem nb055_fresh_065 (x : Var) (y : Var) : (nb055_alpha_dummy_041 x y) ∉ (((Class.cv (nb055_alpha_dummy_032 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_032 x y))).fv) := by
  simpa only [nb055_alpha_dummy_041] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_032 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_032 x y))).fv) 0

theorem nb055_fresh_066 (x : Var) (y : Var) : (nb055_alpha_dummy_037 x y) ∉ (((Class.cv (nb055_alpha_dummy_032 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_033 x y))).fv) := by
  simpa only [nb055_alpha_dummy_037] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_032 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_033 x y))).fv) 0

theorem nb055_fresh_067 (x : Var) (y : Var) : (nb055_alpha_dummy_043 x y) ∉ (((Class.cv (nb055_alpha_dummy_033 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_033 x y))).fv) := by
  simpa only [nb055_alpha_dummy_043] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_033 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_033 x y))).fv) 0

theorem nb055_fresh_068 : (nb055_alpha_dummy_056) ∉ (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_056] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 0

theorem nb055_fresh_069 : (nb055_alpha_dummy_057) ∉ (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_057] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 1

theorem nb055_fresh_070 : (nb055_alpha_dummy_058) ∉ (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_058] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 2

theorem nb055_distinct_071 : (nb055_alpha_dummy_056) ≠ (nb055_alpha_dummy_057) := by
  simpa only [nb055_alpha_dummy_056, nb055_alpha_dummy_057] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb055_distinct_072 : (nb055_alpha_dummy_056) ≠ (nb055_alpha_dummy_058) := by
  simpa only [nb055_alpha_dummy_056, nb055_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb055_distinct_073 : (nb055_alpha_dummy_057) ≠ (nb055_alpha_dummy_058) := by
  simpa only [nb055_alpha_dummy_057, nb055_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb055_fresh_074 (x : Var) (y : Var) : (nb055_alpha_dummy_059 x y) ∉ (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_059] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb055_fresh_075 (x : Var) (y : Var) : (nb055_alpha_dummy_060 x y) ∉ (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_060] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb055_fresh_076 (x : Var) (y : Var) : (nb055_alpha_dummy_061 x y) ∉ (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_061] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb055_distinct_077 (x : Var) (y : Var) : (nb055_alpha_dummy_059 x y) ≠ (nb055_alpha_dummy_060 x y) := by
  simpa only [nb055_alpha_dummy_059, nb055_alpha_dummy_060] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb055_distinct_078 (x : Var) (y : Var) : (nb055_alpha_dummy_059 x y) ≠ (nb055_alpha_dummy_061 x y) := by
  simpa only [nb055_alpha_dummy_059, nb055_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb055_distinct_079 (x : Var) (y : Var) : (nb055_alpha_dummy_060 x y) ≠ (nb055_alpha_dummy_061 x y) := by
  simpa only [nb055_alpha_dummy_060, nb055_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb055_fresh_080 : (nb055_alpha_dummy_068) ∉ (((Class.cv (nb055_alpha_dummy_057))).fv ∪ ((Class.cv (nb055_alpha_dummy_057))).fv) := by
  simpa only [nb055_alpha_dummy_068] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_057))).fv ∪ ((Class.cv (nb055_alpha_dummy_057))).fv) 0

theorem nb055_fresh_081 : (nb055_alpha_dummy_064) ∉ (((Class.cv (nb055_alpha_dummy_057))).fv ∪ ((Class.cv (nb055_alpha_dummy_058))).fv) := by
  simpa only [nb055_alpha_dummy_064] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_057))).fv ∪ ((Class.cv (nb055_alpha_dummy_058))).fv) 0

theorem nb055_fresh_082 : (nb055_alpha_dummy_070) ∉ (((Class.cv (nb055_alpha_dummy_058))).fv ∪ ((Class.cv (nb055_alpha_dummy_058))).fv) := by
  simpa only [nb055_alpha_dummy_070] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_058))).fv ∪ ((Class.cv (nb055_alpha_dummy_058))).fv) 0

theorem nb055_fresh_083 (x : Var) (y : Var) : (nb055_alpha_dummy_069 x y) ∉ (((Class.cv (nb055_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_060 x y))).fv) := by
  simpa only [nb055_alpha_dummy_069] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_060 x y))).fv) 0

theorem nb055_fresh_084 (x : Var) (y : Var) : (nb055_alpha_dummy_065 x y) ∉ (((Class.cv (nb055_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_061 x y))).fv) := by
  simpa only [nb055_alpha_dummy_065] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_061 x y))).fv) 0

theorem nb055_fresh_085 (x : Var) (y : Var) : (nb055_alpha_dummy_071 x y) ∉ (((Class.cv (nb055_alpha_dummy_061 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_061 x y))).fv) := by
  simpa only [nb055_alpha_dummy_071] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_061 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_061 x y))).fv) 0

theorem nb055_fresh_086 : (nb055_alpha_dummy_154) ∉ (((Class.cv (nb055_alpha_dummy_078))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) := by
  simpa only [nb055_alpha_dummy_154] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_078))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) 0

theorem nb055_fresh_087 : (nb055_alpha_dummy_155) ∉ (((Class.cv (nb055_alpha_dummy_078))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) := by
  simpa only [nb055_alpha_dummy_155] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_078))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) 1

theorem nb055_distinct_088 : (nb055_alpha_dummy_154) ≠ (nb055_alpha_dummy_155) := by
  simpa only [nb055_alpha_dummy_154, nb055_alpha_dummy_155] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_078))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_089 (x : Var) (y : Var) : (nb055_alpha_dummy_156 x y) ∉ (((Class.cv (nb055_alpha_dummy_079 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_017 x y))).fv) := by
  simpa only [nb055_alpha_dummy_156] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_079 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_017 x y))).fv) 0

theorem nb055_fresh_090 (x : Var) (y : Var) : (nb055_alpha_dummy_157 x y) ∉ (((Class.cv (nb055_alpha_dummy_079 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_017 x y))).fv) := by
  simpa only [nb055_alpha_dummy_157] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_079 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_017 x y))).fv) 1

theorem nb055_distinct_091 (x : Var) (y : Var) : (nb055_alpha_dummy_156 x y) ≠ (nb055_alpha_dummy_157 x y) := by
  simpa only [nb055_alpha_dummy_156, nb055_alpha_dummy_157] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_079 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_017 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_092 : (nb055_alpha_dummy_090) ∉ (((Class.cv (nb055_alpha_dummy_083))).fv) := by
  simpa only [nb055_alpha_dummy_090] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_083))).fv) 0

theorem nb055_fresh_093 : (nb055_alpha_dummy_091) ∉ (((Class.cv (nb055_alpha_dummy_083))).fv) := by
  simpa only [nb055_alpha_dummy_091] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_083))).fv) 1

theorem nb055_distinct_094 : (nb055_alpha_dummy_090) ≠ (nb055_alpha_dummy_091) := by
  simpa only [nb055_alpha_dummy_090, nb055_alpha_dummy_091] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_083))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_095 (x : Var) (y : Var) : (nb055_alpha_dummy_092 x y) ∉ (((Class.cv (nb055_alpha_dummy_085 x y))).fv) := by
  simpa only [nb055_alpha_dummy_092] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_085 x y))).fv) 0

theorem nb055_fresh_096 (x : Var) (y : Var) : (nb055_alpha_dummy_093 x y) ∉ (((Class.cv (nb055_alpha_dummy_085 x y))).fv) := by
  simpa only [nb055_alpha_dummy_093] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_085 x y))).fv) 1

theorem nb055_distinct_097 (x : Var) (y : Var) : (nb055_alpha_dummy_092 x y) ≠ (nb055_alpha_dummy_093 x y) := by
  simpa only [nb055_alpha_dummy_092, nb055_alpha_dummy_093] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_085 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_098 : (nb055_alpha_dummy_096) ∉ (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_096] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) 0

theorem nb055_fresh_099 : (nb055_alpha_dummy_097) ∉ (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_097] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) 1

theorem nb055_fresh_100 : (nb055_alpha_dummy_098) ∉ (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_098] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) 2

theorem nb055_distinct_101 : (nb055_alpha_dummy_096) ≠ (nb055_alpha_dummy_097) := by
  simpa only [nb055_alpha_dummy_096, nb055_alpha_dummy_097] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb055_distinct_102 : (nb055_alpha_dummy_096) ≠ (nb055_alpha_dummy_098) := by
  simpa only [nb055_alpha_dummy_096, nb055_alpha_dummy_098] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb055_distinct_103 : (nb055_alpha_dummy_097) ≠ (nb055_alpha_dummy_098) := by
  simpa only [nb055_alpha_dummy_097, nb055_alpha_dummy_098] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb055_fresh_104 (x : Var) (y : Var) : (nb055_alpha_dummy_099 x y) ∉ (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_099] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb055_fresh_105 (x : Var) (y : Var) : (nb055_alpha_dummy_100 x y) ∉ (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_100] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb055_fresh_106 (x : Var) (y : Var) : (nb055_alpha_dummy_101 x y) ∉ (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_101] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb055_distinct_107 (x : Var) (y : Var) : (nb055_alpha_dummy_099 x y) ≠ (nb055_alpha_dummy_100 x y) := by
  simpa only [nb055_alpha_dummy_099, nb055_alpha_dummy_100] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb055_distinct_108 (x : Var) (y : Var) : (nb055_alpha_dummy_099 x y) ≠ (nb055_alpha_dummy_101 x y) := by
  simpa only [nb055_alpha_dummy_099, nb055_alpha_dummy_101] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb055_distinct_109 (x : Var) (y : Var) : (nb055_alpha_dummy_100 x y) ≠ (nb055_alpha_dummy_101 x y) := by
  simpa only [nb055_alpha_dummy_100, nb055_alpha_dummy_101] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
