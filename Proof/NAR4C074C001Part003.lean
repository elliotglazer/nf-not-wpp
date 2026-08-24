import NAR4C074C001Part002

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

theorem nb074_distinct_141 (x : Var) : (nb074_alpha_dummy_007 x) ≠ (nb074_alpha_dummy_008 x) := by
  simpa only [nb074_alpha_dummy_007, nb074_alpha_dummy_008] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb074_alpha_dummy_002 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_142 : (nb074_alpha_dummy_017) ∉ (((Wff.classMem (Class.cv (nb074_alpha_dummy_013)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_013)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_013))).fv) := by
  simpa only [nb074_alpha_dummy_017] using freshVar_not_mem (((Wff.classMem (Class.cv (nb074_alpha_dummy_013)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_013)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_013))).fv) 0

theorem nb074_fresh_143 (x : Var) : (nb074_alpha_dummy_018 x) ∉ (((Wff.classMem (Class.cv (nb074_alpha_dummy_015 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_015 x)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_015 x))).fv) := by
  simpa only [nb074_alpha_dummy_018] using freshVar_not_mem (((Wff.classMem (Class.cv (nb074_alpha_dummy_015 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_015 x)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_015 x))).fv) 0

theorem nb074_fresh_144 : (nb074_alpha_dummy_057) ∉ (((Wff.classMem (Class.cv (nb074_alpha_dummy_053)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_053)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_053))).fv) := by
  simpa only [nb074_alpha_dummy_057] using freshVar_not_mem (((Wff.classMem (Class.cv (nb074_alpha_dummy_053)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_053)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_053))).fv) 0

theorem nb074_fresh_145 (x : Var) : (nb074_alpha_dummy_058 x) ∉ (((Wff.classMem (Class.cv (nb074_alpha_dummy_055 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_055 x)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_055 x))).fv) := by
  simpa only [nb074_alpha_dummy_058] using freshVar_not_mem (((Wff.classMem (Class.cv (nb074_alpha_dummy_055 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_055 x)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_055 x))).fv) 0

theorem nb074_fresh_146 : (nb074_alpha_dummy_099) ∉ (((Wff.classMem (Class.cv (nb074_alpha_dummy_095)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_095)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_095))).fv) := by
  simpa only [nb074_alpha_dummy_099] using freshVar_not_mem (((Wff.classMem (Class.cv (nb074_alpha_dummy_095)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_095)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_095))).fv) 0

theorem nb074_fresh_147 (x : Var) : (nb074_alpha_dummy_100 x) ∉ (((Wff.classMem (Class.cv (nb074_alpha_dummy_097 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_097 x)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_097 x))).fv) := by
  simpa only [nb074_alpha_dummy_100] using freshVar_not_mem (((Wff.classMem (Class.cv (nb074_alpha_dummy_097 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_097 x)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_097 x))).fv) 0

theorem nb074_fresh_148 : (nb074_alpha_dummy_135) ∉ (((Wff.classMem (Class.cv (nb074_alpha_dummy_131)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_131)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_131))).fv) := by
  simpa only [nb074_alpha_dummy_135] using freshVar_not_mem (((Wff.classMem (Class.cv (nb074_alpha_dummy_131)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_131)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_131))).fv) 0

theorem nb074_fresh_149 (x : Var) : (nb074_alpha_dummy_136 x) ∉ (((Wff.classMem (Class.cv (nb074_alpha_dummy_133 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_133 x)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_133 x))).fv) := by
  simpa only [nb074_alpha_dummy_136] using freshVar_not_mem (((Wff.classMem (Class.cv (nb074_alpha_dummy_133 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_133 x)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_133 x))).fv) 0

theorem nb074_fresh_150 : (nb074_alpha_dummy_041) ∉ (((syn_ccnv (Class.cv (nb074_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb074_alpha_dummy_041] using freshVar_not_mem (((syn_ccnv (Class.cv (nb074_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) 0

theorem nb074_fresh_151 : (nb074_alpha_dummy_042) ∉ (((syn_ccnv (Class.cv (nb074_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb074_alpha_dummy_042] using freshVar_not_mem (((syn_ccnv (Class.cv (nb074_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) 1

theorem nb074_distinct_152 : (nb074_alpha_dummy_041) ≠ (nb074_alpha_dummy_042) := by
  simpa only [nb074_alpha_dummy_041, nb074_alpha_dummy_042] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb074_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_153 (x : Var) : (nb074_alpha_dummy_043 x) ∉ (((syn_ccnv (Class.cv x))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb074_alpha_dummy_043] using freshVar_not_mem (((syn_ccnv (Class.cv x))).fv ∪ ((syn_cvv)).fv) 0

theorem nb074_fresh_154 (x : Var) : (nb074_alpha_dummy_044 x) ∉ (((syn_ccnv (Class.cv x))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb074_alpha_dummy_044] using freshVar_not_mem (((syn_ccnv (Class.cv x))).fv ∪ ((syn_cvv)).fv) 1

theorem nb074_distinct_155 (x : Var) : (nb074_alpha_dummy_043 x) ≠ (nb074_alpha_dummy_044 x) := by
  simpa only [nb074_alpha_dummy_043, nb074_alpha_dummy_044] using
    (freshVar_injective (((syn_ccnv (Class.cv x))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_156 : (nb074_alpha_dummy_009) ∉ (((syn_ccompl (Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cphi (Class.cv (nb074_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb074_alpha_dummy_009] using freshVar_not_mem (((syn_ccompl (Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cphi (Class.cv (nb074_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb074_fresh_157 (x : Var) : (nb074_alpha_dummy_010 x) ∉ (((syn_ccompl (Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb074_alpha_dummy_010] using freshVar_not_mem (((syn_ccompl (Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb074_fresh_158 : (nb074_alpha_dummy_049) ∉ (((syn_ccompl (Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cphi (Class.cv (nb074_alpha_dummy_046)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb074_alpha_dummy_049] using freshVar_not_mem (((syn_ccompl (Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cphi (Class.cv (nb074_alpha_dummy_046)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb074_fresh_159 (x : Var) : (nb074_alpha_dummy_050 x) ∉ (((syn_ccompl (Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb074_alpha_dummy_050] using freshVar_not_mem (((syn_ccompl (Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb074_fresh_160 : (nb074_alpha_dummy_091) ∉ (((syn_ccompl (Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cphi (Class.cv (nb074_alpha_dummy_088)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb074_alpha_dummy_091] using freshVar_not_mem (((syn_ccompl (Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cphi (Class.cv (nb074_alpha_dummy_088)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb074_fresh_161 (x : Var) : (nb074_alpha_dummy_092 x) ∉ (((syn_ccompl (Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb074_alpha_dummy_092] using freshVar_not_mem (((syn_ccompl (Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb074_fresh_162 : (nb074_alpha_dummy_127) ∉ (((syn_ccompl (Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cphi (Class.cv (nb074_alpha_dummy_124)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb074_alpha_dummy_127] using freshVar_not_mem (((syn_ccompl (Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cphi (Class.cv (nb074_alpha_dummy_124)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb074_fresh_163 (x : Var) : (nb074_alpha_dummy_128 x) ∉ (((syn_ccompl (Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb074_alpha_dummy_128] using freshVar_not_mem (((syn_ccompl (Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb074_fresh_164 : (nb074_alpha_dummy_029) ∉ (((syn_ccompl (Class.cv (nb074_alpha_dummy_020)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_021)))).fv) := by
  simpa only [nb074_alpha_dummy_029] using freshVar_not_mem (((syn_ccompl (Class.cv (nb074_alpha_dummy_020)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_021)))).fv) 0

theorem nb074_fresh_165 (x : Var) : (nb074_alpha_dummy_030 x) ∉ (((syn_ccompl (Class.cv (nb074_alpha_dummy_023 x)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_024 x)))).fv) := by
  simpa only [nb074_alpha_dummy_030] using freshVar_not_mem (((syn_ccompl (Class.cv (nb074_alpha_dummy_023 x)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_024 x)))).fv) 0

theorem nb074_fresh_166 : (nb074_alpha_dummy_069) ∉ (((syn_ccompl (Class.cv (nb074_alpha_dummy_060)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_061)))).fv) := by
  simpa only [nb074_alpha_dummy_069] using freshVar_not_mem (((syn_ccompl (Class.cv (nb074_alpha_dummy_060)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_061)))).fv) 0

theorem nb074_fresh_167 (x : Var) : (nb074_alpha_dummy_070 x) ∉ (((syn_ccompl (Class.cv (nb074_alpha_dummy_063 x)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_064 x)))).fv) := by
  simpa only [nb074_alpha_dummy_070] using freshVar_not_mem (((syn_ccompl (Class.cv (nb074_alpha_dummy_063 x)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_064 x)))).fv) 0

theorem nb074_fresh_168 : (nb074_alpha_dummy_111) ∉ (((syn_ccompl (Class.cv (nb074_alpha_dummy_102)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_103)))).fv) := by
  simpa only [nb074_alpha_dummy_111] using freshVar_not_mem (((syn_ccompl (Class.cv (nb074_alpha_dummy_102)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_103)))).fv) 0

theorem nb074_fresh_169 (x : Var) : (nb074_alpha_dummy_112 x) ∉ (((syn_ccompl (Class.cv (nb074_alpha_dummy_105 x)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_106 x)))).fv) := by
  simpa only [nb074_alpha_dummy_112] using freshVar_not_mem (((syn_ccompl (Class.cv (nb074_alpha_dummy_105 x)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_106 x)))).fv) 0

theorem nb074_fresh_170 : (nb074_alpha_dummy_147) ∉ (((syn_ccompl (Class.cv (nb074_alpha_dummy_138)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_139)))).fv) := by
  simpa only [nb074_alpha_dummy_147] using freshVar_not_mem (((syn_ccompl (Class.cv (nb074_alpha_dummy_138)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_139)))).fv) 0

theorem nb074_fresh_171 (x : Var) : (nb074_alpha_dummy_148 x) ∉ (((syn_ccompl (Class.cv (nb074_alpha_dummy_141 x)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_142 x)))).fv) := by
  simpa only [nb074_alpha_dummy_148] using freshVar_not_mem (((syn_ccompl (Class.cv (nb074_alpha_dummy_141 x)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_142 x)))).fv) 0

theorem nb074_fresh_172 : (nb074_alpha_dummy_037) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_006))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb074_alpha_dummy_037] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_006))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb074_fresh_173 (x : Var) : (nb074_alpha_dummy_038 x) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb074_alpha_dummy_038] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb074_fresh_174 : (nb074_alpha_dummy_077) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_046))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb074_alpha_dummy_077] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_046))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb074_fresh_175 (x : Var) : (nb074_alpha_dummy_078 x) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb074_alpha_dummy_078] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb074_fresh_176 : (nb074_alpha_dummy_119) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_088))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb074_alpha_dummy_119] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_088))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb074_fresh_177 (x : Var) : (nb074_alpha_dummy_120 x) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb074_alpha_dummy_120] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb074_fresh_178 : (nb074_alpha_dummy_155) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_124))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb074_alpha_dummy_155] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_124))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb074_fresh_179 (x : Var) : (nb074_alpha_dummy_156 x) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb074_alpha_dummy_156] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb074_fresh_180 : (nb074_alpha_dummy_025) ∉ (((syn_cnin (Class.cv (nb074_alpha_dummy_020)) (Class.cv (nb074_alpha_dummy_021)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_020)) (Class.cv (nb074_alpha_dummy_021)))).fv) := by
  simpa only [nb074_alpha_dummy_025] using freshVar_not_mem (((syn_cnin (Class.cv (nb074_alpha_dummy_020)) (Class.cv (nb074_alpha_dummy_021)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_020)) (Class.cv (nb074_alpha_dummy_021)))).fv) 0

theorem nb074_fresh_181 (x : Var) : (nb074_alpha_dummy_026 x) ∉ (((syn_cnin (Class.cv (nb074_alpha_dummy_023 x)) (Class.cv (nb074_alpha_dummy_024 x)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_023 x)) (Class.cv (nb074_alpha_dummy_024 x)))).fv) := by
  simpa only [nb074_alpha_dummy_026] using freshVar_not_mem (((syn_cnin (Class.cv (nb074_alpha_dummy_023 x)) (Class.cv (nb074_alpha_dummy_024 x)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_023 x)) (Class.cv (nb074_alpha_dummy_024 x)))).fv) 0

theorem nb074_fresh_182 : (nb074_alpha_dummy_065) ∉ (((syn_cnin (Class.cv (nb074_alpha_dummy_060)) (Class.cv (nb074_alpha_dummy_061)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_060)) (Class.cv (nb074_alpha_dummy_061)))).fv) := by
  simpa only [nb074_alpha_dummy_065] using freshVar_not_mem (((syn_cnin (Class.cv (nb074_alpha_dummy_060)) (Class.cv (nb074_alpha_dummy_061)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_060)) (Class.cv (nb074_alpha_dummy_061)))).fv) 0

theorem nb074_fresh_183 (x : Var) : (nb074_alpha_dummy_066 x) ∉ (((syn_cnin (Class.cv (nb074_alpha_dummy_063 x)) (Class.cv (nb074_alpha_dummy_064 x)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_063 x)) (Class.cv (nb074_alpha_dummy_064 x)))).fv) := by
  simpa only [nb074_alpha_dummy_066] using freshVar_not_mem (((syn_cnin (Class.cv (nb074_alpha_dummy_063 x)) (Class.cv (nb074_alpha_dummy_064 x)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_063 x)) (Class.cv (nb074_alpha_dummy_064 x)))).fv) 0

theorem nb074_fresh_184 : (nb074_alpha_dummy_107) ∉ (((syn_cnin (Class.cv (nb074_alpha_dummy_102)) (Class.cv (nb074_alpha_dummy_103)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_102)) (Class.cv (nb074_alpha_dummy_103)))).fv) := by
  simpa only [nb074_alpha_dummy_107] using freshVar_not_mem (((syn_cnin (Class.cv (nb074_alpha_dummy_102)) (Class.cv (nb074_alpha_dummy_103)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_102)) (Class.cv (nb074_alpha_dummy_103)))).fv) 0

theorem nb074_fresh_185 (x : Var) : (nb074_alpha_dummy_108 x) ∉ (((syn_cnin (Class.cv (nb074_alpha_dummy_105 x)) (Class.cv (nb074_alpha_dummy_106 x)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_105 x)) (Class.cv (nb074_alpha_dummy_106 x)))).fv) := by
  simpa only [nb074_alpha_dummy_108] using freshVar_not_mem (((syn_cnin (Class.cv (nb074_alpha_dummy_105 x)) (Class.cv (nb074_alpha_dummy_106 x)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_105 x)) (Class.cv (nb074_alpha_dummy_106 x)))).fv) 0

theorem nb074_fresh_186 : (nb074_alpha_dummy_143) ∉ (((syn_cnin (Class.cv (nb074_alpha_dummy_138)) (Class.cv (nb074_alpha_dummy_139)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_138)) (Class.cv (nb074_alpha_dummy_139)))).fv) := by
  simpa only [nb074_alpha_dummy_143] using freshVar_not_mem (((syn_cnin (Class.cv (nb074_alpha_dummy_138)) (Class.cv (nb074_alpha_dummy_139)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_138)) (Class.cv (nb074_alpha_dummy_139)))).fv) 0

theorem nb074_fresh_187 (x : Var) : (nb074_alpha_dummy_144 x) ∉ (((syn_cnin (Class.cv (nb074_alpha_dummy_141 x)) (Class.cv (nb074_alpha_dummy_142 x)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_141 x)) (Class.cv (nb074_alpha_dummy_142 x)))).fv) := by
  simpa only [nb074_alpha_dummy_144] using freshVar_not_mem (((syn_cnin (Class.cv (nb074_alpha_dummy_141 x)) (Class.cv (nb074_alpha_dummy_142 x)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_141 x)) (Class.cv (nb074_alpha_dummy_142 x)))).fv) 0

theorem nb074_fresh_188 : (nb074_alpha_dummy_039) ∉ (((syn_cphi (Class.cv (nb074_alpha_dummy_006)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_006)))).fv) := by
  simpa only [nb074_alpha_dummy_039] using freshVar_not_mem (((syn_cphi (Class.cv (nb074_alpha_dummy_006)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_006)))).fv) 0

theorem nb074_fresh_189 (x : Var) : (nb074_alpha_dummy_040 x) ∉ (((syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))).fv) := by
  simpa only [nb074_alpha_dummy_040] using freshVar_not_mem (((syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))).fv) 0

theorem nb074_fresh_190 : (nb074_alpha_dummy_079) ∉ (((syn_cphi (Class.cv (nb074_alpha_dummy_046)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_046)))).fv) := by
  simpa only [nb074_alpha_dummy_079] using freshVar_not_mem (((syn_cphi (Class.cv (nb074_alpha_dummy_046)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_046)))).fv) 0

theorem nb074_fresh_191 (x : Var) : (nb074_alpha_dummy_080 x) ∉ (((syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))).fv) := by
  simpa only [nb074_alpha_dummy_080] using freshVar_not_mem (((syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))).fv) 0

theorem nb074_fresh_192 : (nb074_alpha_dummy_121) ∉ (((syn_cphi (Class.cv (nb074_alpha_dummy_088)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_088)))).fv) := by
  simpa only [nb074_alpha_dummy_121] using freshVar_not_mem (((syn_cphi (Class.cv (nb074_alpha_dummy_088)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_088)))).fv) 0

theorem nb074_fresh_193 (x : Var) : (nb074_alpha_dummy_122 x) ∉ (((syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))).fv) := by
  simpa only [nb074_alpha_dummy_122] using freshVar_not_mem (((syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))).fv) 0

theorem nb074_fresh_194 : (nb074_alpha_dummy_157) ∉ (((syn_cphi (Class.cv (nb074_alpha_dummy_124)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_124)))).fv) := by
  simpa only [nb074_alpha_dummy_157] using freshVar_not_mem (((syn_cphi (Class.cv (nb074_alpha_dummy_124)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_124)))).fv) 0

theorem nb074_fresh_195 (x : Var) : (nb074_alpha_dummy_158 x) ∉ (((syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))).fv) := by
  simpa only [nb074_alpha_dummy_158] using freshVar_not_mem (((syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))).fv) 0

theorem nb074_fresh_196 : (nb074_alpha_dummy_001) ∉ (({(nb074_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cdm (Class.cv (nb074_alpha_dummy_000)))).fv) := by
  simpa only [nb074_alpha_dummy_001] using freshVar_not_mem (({(nb074_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cdm (Class.cv (nb074_alpha_dummy_000)))).fv) 0

theorem nb074_fresh_197 : (nb074_alpha_dummy_003) ∉ (({(nb074_alpha_dummy_000)} : Finset Var) ∪ ({(nb074_alpha_dummy_001)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb074_alpha_dummy_000)) (syn_cvv)) (Wff.classEq (Class.cv (nb074_alpha_dummy_001)) (syn_cdm (Class.cv (nb074_alpha_dummy_000)))))).fv) := by
  simpa only [nb074_alpha_dummy_003] using freshVar_not_mem (({(nb074_alpha_dummy_000)} : Finset Var) ∪ ({(nb074_alpha_dummy_001)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb074_alpha_dummy_000)) (syn_cvv)) (Wff.classEq (Class.cv (nb074_alpha_dummy_001)) (syn_cdm (Class.cv (nb074_alpha_dummy_000)))))).fv) 0

theorem nb074_fresh_198 : (nb074_alpha_dummy_085) ∉ (({(nb074_alpha_dummy_081)} : Finset Var) ∪ ({(nb074_alpha_dummy_082)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb074_alpha_dummy_082)) (Class.cv (nb074_alpha_dummy_000)) (Class.cv (nb074_alpha_dummy_081)))).fv) := by
  simpa only [nb074_alpha_dummy_085] using freshVar_not_mem (({(nb074_alpha_dummy_081)} : Finset Var) ∪ ({(nb074_alpha_dummy_082)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb074_alpha_dummy_082)) (Class.cv (nb074_alpha_dummy_000)) (Class.cv (nb074_alpha_dummy_081)))).fv) 0

theorem nb074_fresh_199 (x : Var) : (nb074_alpha_dummy_086 x) ∉ (({(nb074_alpha_dummy_083 x)} : Finset Var) ∪ ({(nb074_alpha_dummy_084 x)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb074_alpha_dummy_084 x)) (Class.cv x) (Class.cv (nb074_alpha_dummy_083 x)))).fv) := by
  simpa only [nb074_alpha_dummy_086] using freshVar_not_mem (({(nb074_alpha_dummy_083 x)} : Finset Var) ∪ ({(nb074_alpha_dummy_084 x)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb074_alpha_dummy_084 x)) (Class.cv x) (Class.cv (nb074_alpha_dummy_083 x)))).fv) 0

theorem nb074_fresh_200 (x : Var) : (nb074_alpha_dummy_002 x) ∉ (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cdm (Class.cv x))).fv) := by
  simpa only [nb074_alpha_dummy_002] using freshVar_not_mem (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cdm (Class.cv x))).fv) 0

theorem nb074_fresh_201 (x : Var) : (nb074_alpha_dummy_004 x) ∉ (({x} : Finset Var) ∪ ({(nb074_alpha_dummy_002 x)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classEq (Class.cv (nb074_alpha_dummy_002 x)) (syn_cdm (Class.cv x))))).fv) := by
  simpa only [nb074_alpha_dummy_004] using freshVar_not_mem (({x} : Finset Var) ∪ ({(nb074_alpha_dummy_002 x)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classEq (Class.cv (nb074_alpha_dummy_002 x)) (syn_cdm (Class.cv x))))).fv) 0

theorem nb074_fresh_202 : (nb074_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb074_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb074_support_mem_0000 : (nb074_alpha_dummy_000) ∈ (({(nb074_alpha_dummy_000)} : Finset Var) ∪ ({(nb074_alpha_dummy_001)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb074_alpha_dummy_000)) (syn_cvv)) (Wff.classEq (Class.cv (nb074_alpha_dummy_001)) (syn_cdm (Class.cv (nb074_alpha_dummy_000)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0001 (x : Var) : x ∈ (({x} : Finset Var) ∪ ({(nb074_alpha_dummy_002 x)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classEq (Class.cv (nb074_alpha_dummy_002 x)) (syn_cdm (Class.cv x))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0002 : (nb074_alpha_dummy_001) ∈ (({(nb074_alpha_dummy_000)} : Finset Var) ∪ ({(nb074_alpha_dummy_001)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb074_alpha_dummy_000)) (syn_cvv)) (Wff.classEq (Class.cv (nb074_alpha_dummy_001)) (syn_cdm (Class.cv (nb074_alpha_dummy_000)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0003 (x : Var) : (nb074_alpha_dummy_002 x) ∈ (({x} : Finset Var) ∪ ({(nb074_alpha_dummy_002 x)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classEq (Class.cv (nb074_alpha_dummy_002 x)) (syn_cdm (Class.cv x))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0004 : (nb074_alpha_dummy_000) ∈ (({(nb074_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cdm (Class.cv (nb074_alpha_dummy_000)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0005 (x : Var) : x ∈ (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cdm (Class.cv x))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0006 : (nb074_alpha_dummy_000) ∈ (((Class.cv (nb074_alpha_dummy_000))).fv ∪ ((Class.cv (nb074_alpha_dummy_001))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0007 : (nb074_alpha_dummy_000) ∈ (((syn_ccompl (Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cphi (Class.cv (nb074_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0006) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0006) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0008 (x : Var) : x ∈ (((Class.cv x)).fv ∪ ((Class.cv (nb074_alpha_dummy_002 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0009 (x : Var) : x ∈ (((syn_ccompl (Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0008 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0008 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0010 : (nb074_alpha_dummy_000) ∈ (((Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cphi (Class.cv (nb074_alpha_dummy_006))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cphi (Class.cv (nb074_alpha_dummy_006))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0006) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0006) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0011 (x : Var) : x ∈ (((Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0008 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0008 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0012 : (nb074_alpha_dummy_006) ∈ (((Class.cv (nb074_alpha_dummy_006))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0013 (x : Var) : (nb074_alpha_dummy_008 x) ∈ (((Class.cv (nb074_alpha_dummy_008 x))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0014 : (nb074_alpha_dummy_013) ∈ (((Wff.classMem (Class.cv (nb074_alpha_dummy_013)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_013)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_013))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0015 (x : Var) : (nb074_alpha_dummy_015 x) ∈ (((Wff.classMem (Class.cv (nb074_alpha_dummy_015 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_015 x)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_015 x))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0016 : (nb074_alpha_dummy_013) ∈ (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0017 (x : Var) : (nb074_alpha_dummy_015 x) ∈ (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0018 : (nb074_alpha_dummy_020) ∈ (((syn_cnin (Class.cv (nb074_alpha_dummy_020)) (Class.cv (nb074_alpha_dummy_021)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_020)) (Class.cv (nb074_alpha_dummy_021)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0019 (x : Var) : (nb074_alpha_dummy_023 x) ∈ (((syn_cnin (Class.cv (nb074_alpha_dummy_023 x)) (Class.cv (nb074_alpha_dummy_024 x)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_023 x)) (Class.cv (nb074_alpha_dummy_024 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0020 : (nb074_alpha_dummy_020) ∈ (((Class.cv (nb074_alpha_dummy_020))).fv ∪ ((Class.cv (nb074_alpha_dummy_021))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0021 (x : Var) : (nb074_alpha_dummy_023 x) ∈ (((Class.cv (nb074_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_024 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0022 : (nb074_alpha_dummy_021) ∈ (((syn_cnin (Class.cv (nb074_alpha_dummy_020)) (Class.cv (nb074_alpha_dummy_021)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_020)) (Class.cv (nb074_alpha_dummy_021)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0023 (x : Var) : (nb074_alpha_dummy_024 x) ∈ (((syn_cnin (Class.cv (nb074_alpha_dummy_023 x)) (Class.cv (nb074_alpha_dummy_024 x)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_023 x)) (Class.cv (nb074_alpha_dummy_024 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0024 : (nb074_alpha_dummy_021) ∈ (((Class.cv (nb074_alpha_dummy_020))).fv ∪ ((Class.cv (nb074_alpha_dummy_021))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0025 (x : Var) : (nb074_alpha_dummy_024 x) ∈ (((Class.cv (nb074_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_024 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0026 : (nb074_alpha_dummy_020) ∈ (((syn_ccompl (Class.cv (nb074_alpha_dummy_020)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_021)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0027 (x : Var) : (nb074_alpha_dummy_023 x) ∈ (((syn_ccompl (Class.cv (nb074_alpha_dummy_023 x)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_024 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0028 : (nb074_alpha_dummy_020) ∈ (((Class.cv (nb074_alpha_dummy_020))).fv ∪ ((Class.cv (nb074_alpha_dummy_020))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0029 (x : Var) : (nb074_alpha_dummy_023 x) ∈ (((Class.cv (nb074_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_023 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0030 : (nb074_alpha_dummy_021) ∈ (((syn_ccompl (Class.cv (nb074_alpha_dummy_020)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_021)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0031 (x : Var) : (nb074_alpha_dummy_024 x) ∈ (((syn_ccompl (Class.cv (nb074_alpha_dummy_023 x)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_024 x)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0032 : (nb074_alpha_dummy_021) ∈ (((Class.cv (nb074_alpha_dummy_021))).fv ∪ ((Class.cv (nb074_alpha_dummy_021))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0033 (x : Var) : (nb074_alpha_dummy_024 x) ∈ (((Class.cv (nb074_alpha_dummy_024 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_024 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0034 : (nb074_alpha_dummy_001) ∈ (((Class.cv (nb074_alpha_dummy_000))).fv ∪ ((Class.cv (nb074_alpha_dummy_001))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0035 : (nb074_alpha_dummy_001) ∈ (((syn_ccompl (Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cphi (Class.cv (nb074_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0034) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0034) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0036 (x : Var) : (nb074_alpha_dummy_002 x) ∈ (((Class.cv x)).fv ∪ ((Class.cv (nb074_alpha_dummy_002 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0037 (x : Var) : (nb074_alpha_dummy_002 x) ∈ (((syn_ccompl (Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0036 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0036 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0038 : (nb074_alpha_dummy_001) ∈ (((Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0034) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0034) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0039 (x : Var) : (nb074_alpha_dummy_002 x) ∈ (((Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0036 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0036 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0040 : (nb074_alpha_dummy_006) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_006))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0041 (x : Var) : (nb074_alpha_dummy_008 x) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0042 : (nb074_alpha_dummy_006) ∈ (((syn_cphi (Class.cv (nb074_alpha_dummy_006)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_006)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0043 (x : Var) : (nb074_alpha_dummy_008 x) ∈ (((syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0044 : (nb074_alpha_dummy_042) ∈ (((Class.cv (nb074_alpha_dummy_042))).fv ∪ ((Class.cv (nb074_alpha_dummy_041))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0045 : (nb074_alpha_dummy_042) ∈ (((syn_ccompl (Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cphi (Class.cv (nb074_alpha_dummy_046)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0044) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0044) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0046 (x : Var) : (nb074_alpha_dummy_044 x) ∈ (((Class.cv (nb074_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_043 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0047 (x : Var) : (nb074_alpha_dummy_044 x) ∈ (((syn_ccompl (Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0046 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0046 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0048 : (nb074_alpha_dummy_042) ∈ (((Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cphi (Class.cv (nb074_alpha_dummy_046))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cphi (Class.cv (nb074_alpha_dummy_046))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0044) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0044) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0049 (x : Var) : (nb074_alpha_dummy_044 x) ∈ (((Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0046 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0046 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0050 : (nb074_alpha_dummy_046) ∈ (((Class.cv (nb074_alpha_dummy_046))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0051 (x : Var) : (nb074_alpha_dummy_048 x) ∈ (((Class.cv (nb074_alpha_dummy_048 x))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0052 : (nb074_alpha_dummy_053) ∈ (((Wff.classMem (Class.cv (nb074_alpha_dummy_053)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_053)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_053))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0053 (x : Var) : (nb074_alpha_dummy_055 x) ∈ (((Wff.classMem (Class.cv (nb074_alpha_dummy_055 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_055 x)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_055 x))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0054 : (nb074_alpha_dummy_053) ∈ (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0055 (x : Var) : (nb074_alpha_dummy_055 x) ∈ (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0056 : (nb074_alpha_dummy_060) ∈ (((syn_cnin (Class.cv (nb074_alpha_dummy_060)) (Class.cv (nb074_alpha_dummy_061)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_060)) (Class.cv (nb074_alpha_dummy_061)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0057 (x : Var) : (nb074_alpha_dummy_063 x) ∈ (((syn_cnin (Class.cv (nb074_alpha_dummy_063 x)) (Class.cv (nb074_alpha_dummy_064 x)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_063 x)) (Class.cv (nb074_alpha_dummy_064 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0058 : (nb074_alpha_dummy_060) ∈ (((Class.cv (nb074_alpha_dummy_060))).fv ∪ ((Class.cv (nb074_alpha_dummy_061))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0059 (x : Var) : (nb074_alpha_dummy_063 x) ∈ (((Class.cv (nb074_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_064 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0060 : (nb074_alpha_dummy_061) ∈ (((syn_cnin (Class.cv (nb074_alpha_dummy_060)) (Class.cv (nb074_alpha_dummy_061)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_060)) (Class.cv (nb074_alpha_dummy_061)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0061 (x : Var) : (nb074_alpha_dummy_064 x) ∈ (((syn_cnin (Class.cv (nb074_alpha_dummy_063 x)) (Class.cv (nb074_alpha_dummy_064 x)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_063 x)) (Class.cv (nb074_alpha_dummy_064 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0062 : (nb074_alpha_dummy_061) ∈ (((Class.cv (nb074_alpha_dummy_060))).fv ∪ ((Class.cv (nb074_alpha_dummy_061))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0063 (x : Var) : (nb074_alpha_dummy_064 x) ∈ (((Class.cv (nb074_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_064 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0064 : (nb074_alpha_dummy_060) ∈ (((syn_ccompl (Class.cv (nb074_alpha_dummy_060)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_061)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0065 (x : Var) : (nb074_alpha_dummy_063 x) ∈ (((syn_ccompl (Class.cv (nb074_alpha_dummy_063 x)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_064 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0066 : (nb074_alpha_dummy_060) ∈ (((Class.cv (nb074_alpha_dummy_060))).fv ∪ ((Class.cv (nb074_alpha_dummy_060))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0067 (x : Var) : (nb074_alpha_dummy_063 x) ∈ (((Class.cv (nb074_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_063 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0068 : (nb074_alpha_dummy_061) ∈ (((syn_ccompl (Class.cv (nb074_alpha_dummy_060)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_061)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0069 (x : Var) : (nb074_alpha_dummy_064 x) ∈ (((syn_ccompl (Class.cv (nb074_alpha_dummy_063 x)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_064 x)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0070 : (nb074_alpha_dummy_061) ∈ (((Class.cv (nb074_alpha_dummy_061))).fv ∪ ((Class.cv (nb074_alpha_dummy_061))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0071 (x : Var) : (nb074_alpha_dummy_064 x) ∈ (((Class.cv (nb074_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_064 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0072 : (nb074_alpha_dummy_041) ∈ (((Class.cv (nb074_alpha_dummy_042))).fv ∪ ((Class.cv (nb074_alpha_dummy_041))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0073 : (nb074_alpha_dummy_041) ∈ (((syn_ccompl (Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cphi (Class.cv (nb074_alpha_dummy_046)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0072) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0072) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0074 (x : Var) : (nb074_alpha_dummy_043 x) ∈ (((Class.cv (nb074_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_043 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
