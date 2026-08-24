import NAR4C072C001Part001

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

noncomputable def nb072_alpha_dummy_150 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_139 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_139 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_151 (y : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_142 y H))).fv ∪ ((Class.cv (nb072_alpha_dummy_142 y H))).fv) 0)

noncomputable def nb072_alpha_dummy_152 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_140 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_140 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_153 (y : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_143 y H))).fv ∪ ((Class.cv (nb072_alpha_dummy_143 y H))).fv) 0)

noncomputable def nb072_alpha_dummy_154 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cab (nb072_alpha_dummy_124 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H) (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_124 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H) (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb072_alpha_dummy_155 (y : Var) (H : Class) : Var := (freshVar (((Class.cab (nb072_alpha_dummy_126 y H) (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv (nb072_alpha_dummy_117 y H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_126 y H) (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv (nb072_alpha_dummy_117 y H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb072_alpha_dummy_156 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb072_alpha_dummy_157 (y : Var) (H : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb072_alpha_dummy_158 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))).fv) 0)

noncomputable def nb072_alpha_dummy_159 (y : Var) (H : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))).fv) 0)

noncomputable def nb072_alpha_dummy_160 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_118 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_161 (y : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_119 y H))).fv) 0)

noncomputable def nb072_alpha_dummy_162 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb072_alpha_dummy_163 (x : Var) (y : Var) (H : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb072_alpha_dummy_164 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))).fv) 0)

noncomputable def nb072_alpha_dummy_165 (x : Var) (y : Var) (H : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))).fv) 0)

theorem nb072_fresh_000 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_008 A B R S_cls H) ∉ (((Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))))))).fv) := by
  simpa only [nb072_alpha_dummy_008] using freshVar_not_mem (((Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))))))).fv) 0

theorem nb072_fresh_001 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_032 A B R S_cls H) ∉ (((Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb072_alpha_dummy_032] using freshVar_not_mem (((Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb072_fresh_002 (x : Var) (y : Var) : (nb072_alpha_dummy_009 x y) ∉ (((Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))))))).fv) := by
  simpa only [nb072_alpha_dummy_009] using freshVar_not_mem (((Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))))))).fv) 0

theorem nb072_fresh_003 (x : Var) (y : Var) : (nb072_alpha_dummy_033 x y) ∉ (((Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb072_alpha_dummy_033] using freshVar_not_mem (((Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb072_fresh_004 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_044 A B R S_cls H) ∉ (((Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))))).fv) := by
  simpa only [nb072_alpha_dummy_044] using freshVar_not_mem (((Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))))).fv) 0

theorem nb072_fresh_005 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_114 A B R S_cls H) ∉ (((Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb072_alpha_dummy_114] using freshVar_not_mem (((Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb072_fresh_006 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_045 x y H) ∉ (((Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))))).fv) := by
  simpa only [nb072_alpha_dummy_045] using freshVar_not_mem (((Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))))).fv) 0

theorem nb072_fresh_007 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_115 x y H) ∉ (((Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb072_alpha_dummy_115] using freshVar_not_mem (((Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb072_fresh_008 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_050 A B R S_cls H) ∉ (((Class.cab (nb072_alpha_dummy_048 A B R S_cls H) (Wff.classEq (Class.cab (nb072_alpha_dummy_046 A B R S_cls H) (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)))) (syn_csn (Class.cv (nb072_alpha_dummy_048 A B R S_cls H)))))).fv) := by
  simpa only [nb072_alpha_dummy_050] using freshVar_not_mem (((Class.cab (nb072_alpha_dummy_048 A B R S_cls H) (Wff.classEq (Class.cab (nb072_alpha_dummy_046 A B R S_cls H) (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)))) (syn_csn (Class.cv (nb072_alpha_dummy_048 A B R S_cls H)))))).fv) 0

theorem nb072_fresh_009 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_051 A B R S_cls H) ∉ (((Class.cab (nb072_alpha_dummy_048 A B R S_cls H) (Wff.classEq (Class.cab (nb072_alpha_dummy_046 A B R S_cls H) (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)))) (syn_csn (Class.cv (nb072_alpha_dummy_048 A B R S_cls H)))))).fv) := by
  simpa only [nb072_alpha_dummy_051] using freshVar_not_mem (((Class.cab (nb072_alpha_dummy_048 A B R S_cls H) (Wff.classEq (Class.cab (nb072_alpha_dummy_046 A B R S_cls H) (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)))) (syn_csn (Class.cv (nb072_alpha_dummy_048 A B R S_cls H)))))).fv) 1

theorem nb072_distinct_010 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_050 A B R S_cls H) ≠ (nb072_alpha_dummy_051 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_050, nb072_alpha_dummy_051] using
    (freshVar_injective (((Class.cab (nb072_alpha_dummy_048 A B R S_cls H) (Wff.classEq (Class.cab (nb072_alpha_dummy_046 A B R S_cls H) (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)))) (syn_csn (Class.cv (nb072_alpha_dummy_048 A B R S_cls H)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_011 (x : Var) (H : Class) : (nb072_alpha_dummy_052 x H) ∉ (((Class.cab (nb072_alpha_dummy_049 x H) (Wff.classEq (Class.cab (nb072_alpha_dummy_047 x H) (syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H)))) (syn_csn (Class.cv (nb072_alpha_dummy_049 x H)))))).fv) := by
  simpa only [nb072_alpha_dummy_052] using freshVar_not_mem (((Class.cab (nb072_alpha_dummy_049 x H) (Wff.classEq (Class.cab (nb072_alpha_dummy_047 x H) (syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H)))) (syn_csn (Class.cv (nb072_alpha_dummy_049 x H)))))).fv) 0

theorem nb072_fresh_012 (x : Var) (H : Class) : (nb072_alpha_dummy_053 x H) ∉ (((Class.cab (nb072_alpha_dummy_049 x H) (Wff.classEq (Class.cab (nb072_alpha_dummy_047 x H) (syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H)))) (syn_csn (Class.cv (nb072_alpha_dummy_049 x H)))))).fv) := by
  simpa only [nb072_alpha_dummy_053] using freshVar_not_mem (((Class.cab (nb072_alpha_dummy_049 x H) (Wff.classEq (Class.cab (nb072_alpha_dummy_047 x H) (syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H)))) (syn_csn (Class.cv (nb072_alpha_dummy_049 x H)))))).fv) 1

theorem nb072_distinct_013 (x : Var) (H : Class) : (nb072_alpha_dummy_052 x H) ≠ (nb072_alpha_dummy_053 x H) := by
  simpa only [nb072_alpha_dummy_052, nb072_alpha_dummy_053] using
    (freshVar_injective (((Class.cab (nb072_alpha_dummy_049 x H) (Wff.classEq (Class.cab (nb072_alpha_dummy_047 x H) (syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H)))) (syn_csn (Class.cv (nb072_alpha_dummy_049 x H)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_014 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_060 A B R S_cls H) ∉ (((Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))))).fv) := by
  simpa only [nb072_alpha_dummy_060] using freshVar_not_mem (((Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))))).fv) 0

theorem nb072_fresh_015 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_084 A B R S_cls H) ∉ (((Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb072_alpha_dummy_084] using freshVar_not_mem (((Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb072_fresh_016 (x : Var) (H : Class) : (nb072_alpha_dummy_085 x H) ∉ (((Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb072_alpha_dummy_085] using freshVar_not_mem (((Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb072_fresh_017 (x : Var) (H : Class) : (nb072_alpha_dummy_061 x H) ∉ (((Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))))).fv) := by
  simpa only [nb072_alpha_dummy_061] using freshVar_not_mem (((Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))))).fv) 0

theorem nb072_fresh_018 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_120 A B R S_cls H) ∉ (((Class.cab (nb072_alpha_dummy_118 A B R S_cls H) (Wff.classEq (Class.cab (nb072_alpha_dummy_116 A B R S_cls H) (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)))) (syn_csn (Class.cv (nb072_alpha_dummy_118 A B R S_cls H)))))).fv) := by
  simpa only [nb072_alpha_dummy_120] using freshVar_not_mem (((Class.cab (nb072_alpha_dummy_118 A B R S_cls H) (Wff.classEq (Class.cab (nb072_alpha_dummy_116 A B R S_cls H) (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)))) (syn_csn (Class.cv (nb072_alpha_dummy_118 A B R S_cls H)))))).fv) 0

theorem nb072_fresh_019 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_121 A B R S_cls H) ∉ (((Class.cab (nb072_alpha_dummy_118 A B R S_cls H) (Wff.classEq (Class.cab (nb072_alpha_dummy_116 A B R S_cls H) (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)))) (syn_csn (Class.cv (nb072_alpha_dummy_118 A B R S_cls H)))))).fv) := by
  simpa only [nb072_alpha_dummy_121] using freshVar_not_mem (((Class.cab (nb072_alpha_dummy_118 A B R S_cls H) (Wff.classEq (Class.cab (nb072_alpha_dummy_116 A B R S_cls H) (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)))) (syn_csn (Class.cv (nb072_alpha_dummy_118 A B R S_cls H)))))).fv) 1

theorem nb072_distinct_020 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_120 A B R S_cls H) ≠ (nb072_alpha_dummy_121 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_120, nb072_alpha_dummy_121] using
    (freshVar_injective (((Class.cab (nb072_alpha_dummy_118 A B R S_cls H) (Wff.classEq (Class.cab (nb072_alpha_dummy_116 A B R S_cls H) (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)))) (syn_csn (Class.cv (nb072_alpha_dummy_118 A B R S_cls H)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_021 (y : Var) (H : Class) : (nb072_alpha_dummy_122 y H) ∉ (((Class.cab (nb072_alpha_dummy_119 y H) (Wff.classEq (Class.cab (nb072_alpha_dummy_117 y H) (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H)))) (syn_csn (Class.cv (nb072_alpha_dummy_119 y H)))))).fv) := by
  simpa only [nb072_alpha_dummy_122] using freshVar_not_mem (((Class.cab (nb072_alpha_dummy_119 y H) (Wff.classEq (Class.cab (nb072_alpha_dummy_117 y H) (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H)))) (syn_csn (Class.cv (nb072_alpha_dummy_119 y H)))))).fv) 0

theorem nb072_fresh_022 (y : Var) (H : Class) : (nb072_alpha_dummy_123 y H) ∉ (((Class.cab (nb072_alpha_dummy_119 y H) (Wff.classEq (Class.cab (nb072_alpha_dummy_117 y H) (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H)))) (syn_csn (Class.cv (nb072_alpha_dummy_119 y H)))))).fv) := by
  simpa only [nb072_alpha_dummy_123] using freshVar_not_mem (((Class.cab (nb072_alpha_dummy_119 y H) (Wff.classEq (Class.cab (nb072_alpha_dummy_117 y H) (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H)))) (syn_csn (Class.cv (nb072_alpha_dummy_119 y H)))))).fv) 1

theorem nb072_distinct_023 (y : Var) (H : Class) : (nb072_alpha_dummy_122 y H) ≠ (nb072_alpha_dummy_123 y H) := by
  simpa only [nb072_alpha_dummy_122, nb072_alpha_dummy_123] using
    (freshVar_injective (((Class.cab (nb072_alpha_dummy_119 y H) (Wff.classEq (Class.cab (nb072_alpha_dummy_117 y H) (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H)))) (syn_csn (Class.cv (nb072_alpha_dummy_119 y H)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_024 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_130 A B R S_cls H) ∉ (((Class.cab (nb072_alpha_dummy_124 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_124 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))))).fv) := by
  simpa only [nb072_alpha_dummy_130] using freshVar_not_mem (((Class.cab (nb072_alpha_dummy_124 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_124 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))))).fv) 0

theorem nb072_fresh_025 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_154 A B R S_cls H) ∉ (((Class.cab (nb072_alpha_dummy_124 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H) (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_124 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H) (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb072_alpha_dummy_154] using freshVar_not_mem (((Class.cab (nb072_alpha_dummy_124 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H) (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_124 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H) (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb072_fresh_026 (y : Var) (H : Class) : (nb072_alpha_dummy_155 y H) ∉ (((Class.cab (nb072_alpha_dummy_126 y H) (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv (nb072_alpha_dummy_117 y H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_126 y H) (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv (nb072_alpha_dummy_117 y H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb072_alpha_dummy_155] using freshVar_not_mem (((Class.cab (nb072_alpha_dummy_126 y H) (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv (nb072_alpha_dummy_117 y H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_126 y H) (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv (nb072_alpha_dummy_117 y H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb072_fresh_027 (y : Var) (H : Class) : (nb072_alpha_dummy_131 y H) ∉ (((Class.cab (nb072_alpha_dummy_126 y H) (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_126 y H) (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))))).fv) := by
  simpa only [nb072_alpha_dummy_131] using freshVar_not_mem (((Class.cab (nb072_alpha_dummy_126 y H) (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_126 y H) (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))))).fv) 0

theorem nb072_fresh_028 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_002 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_002] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) 0

theorem nb072_fresh_029 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_003 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_003] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) 1

theorem nb072_distinct_030 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_002 A B R S_cls H) ≠ (nb072_alpha_dummy_003 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_002, nb072_alpha_dummy_003] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_031 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_054 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_046 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_054] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_046 A B R S_cls H))).fv) 0

theorem nb072_fresh_032 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_055 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_046 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_055] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_046 A B R S_cls H))).fv) 1

theorem nb072_distinct_033 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_054 A B R S_cls H) ≠ (nb072_alpha_dummy_055 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_054, nb072_alpha_dummy_055] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_046 A B R S_cls H))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_034 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_124 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_116 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_124] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_116 A B R S_cls H))).fv) 0

theorem nb072_fresh_035 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_125 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_116 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_125] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_116 A B R S_cls H))).fv) 1

theorem nb072_distinct_036 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_124 A B R S_cls H) ≠ (nb072_alpha_dummy_125 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_124, nb072_alpha_dummy_125] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_116 A B R S_cls H))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_037 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_010 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_003 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_010] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_003 A B R S_cls H))).fv) 0

theorem nb072_fresh_038 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_011 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_003 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_011] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_003 A B R S_cls H))).fv) 1

theorem nb072_distinct_039 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_010 A B R S_cls H) ≠ (nb072_alpha_dummy_011 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_010, nb072_alpha_dummy_011] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_003 A B R S_cls H))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_040 (x : Var) (y : Var) : (nb072_alpha_dummy_012 x y) ∉ (((Class.cv (nb072_alpha_dummy_005 x y))).fv) := by
  simpa only [nb072_alpha_dummy_012] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_005 x y))).fv) 0

theorem nb072_fresh_041 (x : Var) (y : Var) : (nb072_alpha_dummy_013 x y) ∉ (((Class.cv (nb072_alpha_dummy_005 x y))).fv) := by
  simpa only [nb072_alpha_dummy_013] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_005 x y))).fv) 1

theorem nb072_distinct_042 (x : Var) (y : Var) : (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_013 x y) := by
  simpa only [nb072_alpha_dummy_012, nb072_alpha_dummy_013] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_005 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_043 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_016 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb072_alpha_dummy_016] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 0

theorem nb072_fresh_044 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_017 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb072_alpha_dummy_017] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 1

theorem nb072_fresh_045 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_018 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb072_alpha_dummy_018] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 2

theorem nb072_distinct_046 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_016 A B R S_cls H) ≠ (nb072_alpha_dummy_017 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_016, nb072_alpha_dummy_017] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb072_distinct_047 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_016 A B R S_cls H) ≠ (nb072_alpha_dummy_018 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_016, nb072_alpha_dummy_018] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb072_distinct_048 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_017 A B R S_cls H) ≠ (nb072_alpha_dummy_018 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_017, nb072_alpha_dummy_018] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb072_fresh_049 (x : Var) (y : Var) : (nb072_alpha_dummy_019 x y) ∉ (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb072_alpha_dummy_019] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb072_fresh_050 (x : Var) (y : Var) : (nb072_alpha_dummy_020 x y) ∉ (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb072_alpha_dummy_020] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb072_fresh_051 (x : Var) (y : Var) : (nb072_alpha_dummy_021 x y) ∉ (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb072_alpha_dummy_021] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb072_distinct_052 (x : Var) (y : Var) : (nb072_alpha_dummy_019 x y) ≠ (nb072_alpha_dummy_020 x y) := by
  simpa only [nb072_alpha_dummy_019, nb072_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb072_distinct_053 (x : Var) (y : Var) : (nb072_alpha_dummy_019 x y) ≠ (nb072_alpha_dummy_021 x y) := by
  simpa only [nb072_alpha_dummy_019, nb072_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb072_distinct_054 (x : Var) (y : Var) : (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_021 x y) := by
  simpa only [nb072_alpha_dummy_020, nb072_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb072_fresh_055 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_028 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_028] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv) 0

theorem nb072_fresh_056 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_024 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_024] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv) 0

theorem nb072_fresh_057 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_030 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_030] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv) 0

theorem nb072_fresh_058 (x : Var) (y : Var) : (nb072_alpha_dummy_029 x y) ∉ (((Class.cv (nb072_alpha_dummy_020 x y))).fv ∪ ((Class.cv (nb072_alpha_dummy_020 x y))).fv) := by
  simpa only [nb072_alpha_dummy_029] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_020 x y))).fv ∪ ((Class.cv (nb072_alpha_dummy_020 x y))).fv) 0

theorem nb072_fresh_059 (x : Var) (y : Var) : (nb072_alpha_dummy_025 x y) ∉ (((Class.cv (nb072_alpha_dummy_020 x y))).fv ∪ ((Class.cv (nb072_alpha_dummy_021 x y))).fv) := by
  simpa only [nb072_alpha_dummy_025] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_020 x y))).fv ∪ ((Class.cv (nb072_alpha_dummy_021 x y))).fv) 0

theorem nb072_fresh_060 (x : Var) (y : Var) : (nb072_alpha_dummy_031 x y) ∉ (((Class.cv (nb072_alpha_dummy_021 x y))).fv ∪ ((Class.cv (nb072_alpha_dummy_021 x y))).fv) := by
  simpa only [nb072_alpha_dummy_031] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_021 x y))).fv ∪ ((Class.cv (nb072_alpha_dummy_021 x y))).fv) 0

theorem nb072_fresh_061 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_092 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_039 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_092] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_039 A B R S_cls H))).fv) 0

theorem nb072_fresh_062 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_093 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_039 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_093] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_039 A B R S_cls H))).fv) 1

theorem nb072_distinct_063 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_092 A B R S_cls H) ≠ (nb072_alpha_dummy_093 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_092, nb072_alpha_dummy_093] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_039 A B R S_cls H))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_064 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_094 x y H) ∉ (((Class.cv (nb072_alpha_dummy_041 x y H))).fv) := by
  simpa only [nb072_alpha_dummy_094] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_041 x y H))).fv) 0

theorem nb072_fresh_065 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_095 x y H) ∉ (((Class.cv (nb072_alpha_dummy_041 x y H))).fv) := by
  simpa only [nb072_alpha_dummy_095] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_041 x y H))).fv) 1

theorem nb072_distinct_066 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_094 x y H) ≠ (nb072_alpha_dummy_095 x y H) := by
  simpa only [nb072_alpha_dummy_094, nb072_alpha_dummy_095] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_041 x y H))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_067 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_090 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_048 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_090] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_048 A B R S_cls H))).fv) 0

theorem nb072_fresh_068 (x : Var) (H : Class) : (nb072_alpha_dummy_091 x H) ∉ (((Class.cv (nb072_alpha_dummy_049 x H))).fv) := by
  simpa only [nb072_alpha_dummy_091] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_049 x H))).fv) 0

theorem nb072_fresh_069 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_062 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_055 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_062] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_055 A B R S_cls H))).fv) 0

theorem nb072_fresh_070 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_063 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_055 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_063] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_055 A B R S_cls H))).fv) 1

theorem nb072_distinct_071 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_062 A B R S_cls H) ≠ (nb072_alpha_dummy_063 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_062, nb072_alpha_dummy_063] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_055 A B R S_cls H))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_072 (x : Var) (H : Class) : (nb072_alpha_dummy_064 x H) ∉ (((Class.cv (nb072_alpha_dummy_057 x H))).fv) := by
  simpa only [nb072_alpha_dummy_064] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_057 x H))).fv) 0

theorem nb072_fresh_073 (x : Var) (H : Class) : (nb072_alpha_dummy_065 x H) ∉ (((Class.cv (nb072_alpha_dummy_057 x H))).fv) := by
  simpa only [nb072_alpha_dummy_065] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_057 x H))).fv) 1

theorem nb072_distinct_074 (x : Var) (H : Class) : (nb072_alpha_dummy_064 x H) ≠ (nb072_alpha_dummy_065 x H) := by
  simpa only [nb072_alpha_dummy_064, nb072_alpha_dummy_065] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_057 x H))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_075 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_068 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb072_alpha_dummy_068] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 0

theorem nb072_fresh_076 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_069 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb072_alpha_dummy_069] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 1

theorem nb072_fresh_077 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_070 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb072_alpha_dummy_070] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 2

theorem nb072_distinct_078 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_068 A B R S_cls H) ≠ (nb072_alpha_dummy_069 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_068, nb072_alpha_dummy_069] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb072_distinct_079 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_068 A B R S_cls H) ≠ (nb072_alpha_dummy_070 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_068, nb072_alpha_dummy_070] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb072_distinct_080 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_069 A B R S_cls H) ≠ (nb072_alpha_dummy_070 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_069, nb072_alpha_dummy_070] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb072_fresh_081 (x : Var) (H : Class) : (nb072_alpha_dummy_071 x H) ∉ (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb072_alpha_dummy_071] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) 0

theorem nb072_fresh_082 (x : Var) (H : Class) : (nb072_alpha_dummy_072 x H) ∉ (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb072_alpha_dummy_072] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) 1

theorem nb072_fresh_083 (x : Var) (H : Class) : (nb072_alpha_dummy_073 x H) ∉ (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb072_alpha_dummy_073] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) 2

theorem nb072_distinct_084 (x : Var) (H : Class) : (nb072_alpha_dummy_071 x H) ≠ (nb072_alpha_dummy_072 x H) := by
  simpa only [nb072_alpha_dummy_071, nb072_alpha_dummy_072] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb072_distinct_085 (x : Var) (H : Class) : (nb072_alpha_dummy_071 x H) ≠ (nb072_alpha_dummy_073 x H) := by
  simpa only [nb072_alpha_dummy_071, nb072_alpha_dummy_073] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb072_distinct_086 (x : Var) (H : Class) : (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_073 x H) := by
  simpa only [nb072_alpha_dummy_072, nb072_alpha_dummy_073] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb072_fresh_087 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_080 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_080] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv) 0

theorem nb072_fresh_088 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_076 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_076] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv) 0

theorem nb072_fresh_089 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_082 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_082] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv) 0

theorem nb072_fresh_090 (x : Var) (H : Class) : (nb072_alpha_dummy_081 x H) ∉ (((Class.cv (nb072_alpha_dummy_072 x H))).fv ∪ ((Class.cv (nb072_alpha_dummy_072 x H))).fv) := by
  simpa only [nb072_alpha_dummy_081] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_072 x H))).fv ∪ ((Class.cv (nb072_alpha_dummy_072 x H))).fv) 0

theorem nb072_fresh_091 (x : Var) (H : Class) : (nb072_alpha_dummy_077 x H) ∉ (((Class.cv (nb072_alpha_dummy_072 x H))).fv ∪ ((Class.cv (nb072_alpha_dummy_073 x H))).fv) := by
  simpa only [nb072_alpha_dummy_077] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_072 x H))).fv ∪ ((Class.cv (nb072_alpha_dummy_073 x H))).fv) 0

theorem nb072_fresh_092 (x : Var) (H : Class) : (nb072_alpha_dummy_083 x H) ∉ (((Class.cv (nb072_alpha_dummy_073 x H))).fv ∪ ((Class.cv (nb072_alpha_dummy_073 x H))).fv) := by
  simpa only [nb072_alpha_dummy_083] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_073 x H))).fv ∪ ((Class.cv (nb072_alpha_dummy_073 x H))).fv) 0

theorem nb072_fresh_093 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_098 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb072_alpha_dummy_098] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 0

theorem nb072_fresh_094 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_099 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb072_alpha_dummy_099] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 1

theorem nb072_fresh_095 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_100 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb072_alpha_dummy_100] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 2

theorem nb072_distinct_096 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_098 A B R S_cls H) ≠ (nb072_alpha_dummy_099 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_098, nb072_alpha_dummy_099] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb072_distinct_097 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_098 A B R S_cls H) ≠ (nb072_alpha_dummy_100 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_098, nb072_alpha_dummy_100] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb072_distinct_098 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_099 A B R S_cls H) ≠ (nb072_alpha_dummy_100 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_099, nb072_alpha_dummy_100] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb072_fresh_099 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_101 x y H) ∉ (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb072_alpha_dummy_101] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) 0

theorem nb072_fresh_100 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_102 x y H) ∉ (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb072_alpha_dummy_102] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) 1

theorem nb072_fresh_101 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_103 x y H) ∉ (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb072_alpha_dummy_103] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) 2

theorem nb072_distinct_102 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_101 x y H) ≠ (nb072_alpha_dummy_102 x y H) := by
  simpa only [nb072_alpha_dummy_101, nb072_alpha_dummy_102] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb072_distinct_103 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_101 x y H) ≠ (nb072_alpha_dummy_103 x y H) := by
  simpa only [nb072_alpha_dummy_101, nb072_alpha_dummy_103] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb072_distinct_104 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_103 x y H) := by
  simpa only [nb072_alpha_dummy_102, nb072_alpha_dummy_103] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb072_fresh_105 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_110 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_110] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv) 0

theorem nb072_fresh_106 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_106 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_106] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv) 0

theorem nb072_fresh_107 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_112 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_112] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv) 0

theorem nb072_fresh_108 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_111 x y H) ∉ (((Class.cv (nb072_alpha_dummy_102 x y H))).fv ∪ ((Class.cv (nb072_alpha_dummy_102 x y H))).fv) := by
  simpa only [nb072_alpha_dummy_111] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_102 x y H))).fv ∪ ((Class.cv (nb072_alpha_dummy_102 x y H))).fv) 0

theorem nb072_fresh_109 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_107 x y H) ∉ (((Class.cv (nb072_alpha_dummy_102 x y H))).fv ∪ ((Class.cv (nb072_alpha_dummy_103 x y H))).fv) := by
  simpa only [nb072_alpha_dummy_107] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_102 x y H))).fv ∪ ((Class.cv (nb072_alpha_dummy_103 x y H))).fv) 0

theorem nb072_fresh_110 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_113 x y H) ∉ (((Class.cv (nb072_alpha_dummy_103 x y H))).fv ∪ ((Class.cv (nb072_alpha_dummy_103 x y H))).fv) := by
  simpa only [nb072_alpha_dummy_113] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_103 x y H))).fv ∪ ((Class.cv (nb072_alpha_dummy_103 x y H))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
