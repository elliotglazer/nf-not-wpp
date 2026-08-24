import NAR4C072C001Part002

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

theorem nb072_fresh_111 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_160 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_118 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_160] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_118 A B R S_cls H))).fv) 0

theorem nb072_fresh_112 (y : Var) (H : Class) : (nb072_alpha_dummy_161 y H) ∉ (((Class.cv (nb072_alpha_dummy_119 y H))).fv) := by
  simpa only [nb072_alpha_dummy_161] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_119 y H))).fv) 0

theorem nb072_fresh_113 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_132 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_125 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_132] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_125 A B R S_cls H))).fv) 0

theorem nb072_fresh_114 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_133 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_125 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_133] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_125 A B R S_cls H))).fv) 1

theorem nb072_distinct_115 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_132 A B R S_cls H) ≠ (nb072_alpha_dummy_133 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_132, nb072_alpha_dummy_133] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_125 A B R S_cls H))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_116 (y : Var) (H : Class) : (nb072_alpha_dummy_134 y H) ∉ (((Class.cv (nb072_alpha_dummy_127 y H))).fv) := by
  simpa only [nb072_alpha_dummy_134] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_127 y H))).fv) 0

theorem nb072_fresh_117 (y : Var) (H : Class) : (nb072_alpha_dummy_135 y H) ∉ (((Class.cv (nb072_alpha_dummy_127 y H))).fv) := by
  simpa only [nb072_alpha_dummy_135] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_127 y H))).fv) 1

theorem nb072_distinct_118 (y : Var) (H : Class) : (nb072_alpha_dummy_134 y H) ≠ (nb072_alpha_dummy_135 y H) := by
  simpa only [nb072_alpha_dummy_134, nb072_alpha_dummy_135] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_127 y H))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_119 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_138 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb072_alpha_dummy_138] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 0

theorem nb072_fresh_120 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_139 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb072_alpha_dummy_139] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 1

theorem nb072_fresh_121 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_140 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb072_alpha_dummy_140] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 2

theorem nb072_distinct_122 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_138 A B R S_cls H) ≠ (nb072_alpha_dummy_139 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_138, nb072_alpha_dummy_139] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb072_distinct_123 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_138 A B R S_cls H) ≠ (nb072_alpha_dummy_140 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_138, nb072_alpha_dummy_140] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb072_distinct_124 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_139 A B R S_cls H) ≠ (nb072_alpha_dummy_140 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_139, nb072_alpha_dummy_140] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb072_fresh_125 (y : Var) (H : Class) : (nb072_alpha_dummy_141 y H) ∉ (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb072_alpha_dummy_141] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) 0

theorem nb072_fresh_126 (y : Var) (H : Class) : (nb072_alpha_dummy_142 y H) ∉ (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb072_alpha_dummy_142] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) 1

theorem nb072_fresh_127 (y : Var) (H : Class) : (nb072_alpha_dummy_143 y H) ∉ (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb072_alpha_dummy_143] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) 2

theorem nb072_distinct_128 (y : Var) (H : Class) : (nb072_alpha_dummy_141 y H) ≠ (nb072_alpha_dummy_142 y H) := by
  simpa only [nb072_alpha_dummy_141, nb072_alpha_dummy_142] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb072_distinct_129 (y : Var) (H : Class) : (nb072_alpha_dummy_141 y H) ≠ (nb072_alpha_dummy_143 y H) := by
  simpa only [nb072_alpha_dummy_141, nb072_alpha_dummy_143] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb072_distinct_130 (y : Var) (H : Class) : (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_143 y H) := by
  simpa only [nb072_alpha_dummy_142, nb072_alpha_dummy_143] using
    (freshVar_injective (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb072_fresh_131 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_150 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_139 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_139 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_150] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_139 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_139 A B R S_cls H))).fv) 0

theorem nb072_fresh_132 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_146 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_139 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_140 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_146] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_139 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_140 A B R S_cls H))).fv) 0

theorem nb072_fresh_133 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_152 A B R S_cls H) ∉ (((Class.cv (nb072_alpha_dummy_140 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_140 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_152] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_140 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_140 A B R S_cls H))).fv) 0

theorem nb072_fresh_134 (y : Var) (H : Class) : (nb072_alpha_dummy_151 y H) ∉ (((Class.cv (nb072_alpha_dummy_142 y H))).fv ∪ ((Class.cv (nb072_alpha_dummy_142 y H))).fv) := by
  simpa only [nb072_alpha_dummy_151] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_142 y H))).fv ∪ ((Class.cv (nb072_alpha_dummy_142 y H))).fv) 0

theorem nb072_fresh_135 (y : Var) (H : Class) : (nb072_alpha_dummy_147 y H) ∉ (((Class.cv (nb072_alpha_dummy_142 y H))).fv ∪ ((Class.cv (nb072_alpha_dummy_143 y H))).fv) := by
  simpa only [nb072_alpha_dummy_147] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_142 y H))).fv ∪ ((Class.cv (nb072_alpha_dummy_143 y H))).fv) 0

theorem nb072_fresh_136 (y : Var) (H : Class) : (nb072_alpha_dummy_153 y H) ∉ (((Class.cv (nb072_alpha_dummy_143 y H))).fv ∪ ((Class.cv (nb072_alpha_dummy_143 y H))).fv) := by
  simpa only [nb072_alpha_dummy_153] using freshVar_not_mem (((Class.cv (nb072_alpha_dummy_143 y H))).fv ∪ ((Class.cv (nb072_alpha_dummy_143 y H))).fv) 0

theorem nb072_fresh_137 (x : Var) (H : Class) : (nb072_alpha_dummy_056 x H) ∉ (((Class.cv x)).fv ∪ ((Class.cv (nb072_alpha_dummy_047 x H))).fv) := by
  simpa only [nb072_alpha_dummy_056] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb072_alpha_dummy_047 x H))).fv) 0

theorem nb072_fresh_138 (x : Var) (H : Class) : (nb072_alpha_dummy_057 x H) ∉ (((Class.cv x)).fv ∪ ((Class.cv (nb072_alpha_dummy_047 x H))).fv) := by
  simpa only [nb072_alpha_dummy_057] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb072_alpha_dummy_047 x H))).fv) 1

theorem nb072_distinct_139 (x : Var) (H : Class) : (nb072_alpha_dummy_056 x H) ≠ (nb072_alpha_dummy_057 x H) := by
  simpa only [nb072_alpha_dummy_056, nb072_alpha_dummy_057] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb072_alpha_dummy_047 x H))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_140 (x : Var) (y : Var) : (nb072_alpha_dummy_004 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb072_alpha_dummy_004] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb072_fresh_141 (x : Var) (y : Var) : (nb072_alpha_dummy_005 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb072_alpha_dummy_005] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb072_distinct_142 (x : Var) (y : Var) : (nb072_alpha_dummy_004 x y) ≠ (nb072_alpha_dummy_005 x y) := by
  simpa only [nb072_alpha_dummy_004, nb072_alpha_dummy_005] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_143 (y : Var) (H : Class) : (nb072_alpha_dummy_126 y H) ∉ (((Class.cv y)).fv ∪ ((Class.cv (nb072_alpha_dummy_117 y H))).fv) := by
  simpa only [nb072_alpha_dummy_126] using freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv (nb072_alpha_dummy_117 y H))).fv) 0

theorem nb072_fresh_144 (y : Var) (H : Class) : (nb072_alpha_dummy_127 y H) ∉ (((Class.cv y)).fv ∪ ((Class.cv (nb072_alpha_dummy_117 y H))).fv) := by
  simpa only [nb072_alpha_dummy_127] using freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv (nb072_alpha_dummy_117 y H))).fv) 1

theorem nb072_distinct_145 (y : Var) (H : Class) : (nb072_alpha_dummy_126 y H) ≠ (nb072_alpha_dummy_127 y H) := by
  simpa only [nb072_alpha_dummy_126, nb072_alpha_dummy_127] using
    (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv (nb072_alpha_dummy_117 y H))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_146 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_014 A B R S_cls H) ∉ (((Wff.classMem (Class.cv (nb072_alpha_dummy_010 A B R S_cls H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_010 A B R S_cls H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_014] using freshVar_not_mem (((Wff.classMem (Class.cv (nb072_alpha_dummy_010 A B R S_cls H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_010 A B R S_cls H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv) 0

theorem nb072_fresh_147 (x : Var) (y : Var) : (nb072_alpha_dummy_015 x y) ∉ (((Wff.classMem (Class.cv (nb072_alpha_dummy_012 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_012 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_012 x y))).fv) := by
  simpa only [nb072_alpha_dummy_015] using freshVar_not_mem (((Wff.classMem (Class.cv (nb072_alpha_dummy_012 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_012 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_012 x y))).fv) 0

theorem nb072_fresh_148 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_066 A B R S_cls H) ∉ (((Wff.classMem (Class.cv (nb072_alpha_dummy_062 A B R S_cls H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_062 A B R S_cls H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_066] using freshVar_not_mem (((Wff.classMem (Class.cv (nb072_alpha_dummy_062 A B R S_cls H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_062 A B R S_cls H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv) 0

theorem nb072_fresh_149 (x : Var) (H : Class) : (nb072_alpha_dummy_067 x H) ∉ (((Wff.classMem (Class.cv (nb072_alpha_dummy_064 x H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_064 x H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_064 x H))).fv) := by
  simpa only [nb072_alpha_dummy_067] using freshVar_not_mem (((Wff.classMem (Class.cv (nb072_alpha_dummy_064 x H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_064 x H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_064 x H))).fv) 0

theorem nb072_fresh_150 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_096 A B R S_cls H) ∉ (((Wff.classMem (Class.cv (nb072_alpha_dummy_092 A B R S_cls H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_092 A B R S_cls H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_096] using freshVar_not_mem (((Wff.classMem (Class.cv (nb072_alpha_dummy_092 A B R S_cls H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_092 A B R S_cls H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv) 0

theorem nb072_fresh_151 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_097 x y H) ∉ (((Wff.classMem (Class.cv (nb072_alpha_dummy_094 x y H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_094 x y H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_094 x y H))).fv) := by
  simpa only [nb072_alpha_dummy_097] using freshVar_not_mem (((Wff.classMem (Class.cv (nb072_alpha_dummy_094 x y H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_094 x y H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_094 x y H))).fv) 0

theorem nb072_fresh_152 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_136 A B R S_cls H) ∉ (((Wff.classMem (Class.cv (nb072_alpha_dummy_132 A B R S_cls H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_132 A B R S_cls H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_136] using freshVar_not_mem (((Wff.classMem (Class.cv (nb072_alpha_dummy_132 A B R S_cls H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_132 A B R S_cls H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv) 0

theorem nb072_fresh_153 (y : Var) (H : Class) : (nb072_alpha_dummy_137 y H) ∉ (((Wff.classMem (Class.cv (nb072_alpha_dummy_134 y H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_134 y H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_134 y H))).fv) := by
  simpa only [nb072_alpha_dummy_137] using freshVar_not_mem (((Wff.classMem (Class.cv (nb072_alpha_dummy_134 y H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_134 y H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_134 y H))).fv) 0

theorem nb072_fresh_154 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_006 A B R S_cls H) ∉ (((syn_ccompl (Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb072_alpha_dummy_006] using freshVar_not_mem (((syn_ccompl (Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb072_fresh_155 (x : Var) (y : Var) : (nb072_alpha_dummy_007 x y) ∉ (((syn_ccompl (Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb072_alpha_dummy_007] using freshVar_not_mem (((syn_ccompl (Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb072_fresh_156 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_042 A B R S_cls H) ∉ (((syn_ccompl (Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb072_alpha_dummy_042] using freshVar_not_mem (((syn_ccompl (Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb072_fresh_157 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_043 x y H) ∉ (((syn_ccompl (Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb072_alpha_dummy_043] using freshVar_not_mem (((syn_ccompl (Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb072_fresh_158 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_058 A B R S_cls H) ∉ (((syn_ccompl (Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb072_alpha_dummy_058] using freshVar_not_mem (((syn_ccompl (Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb072_fresh_159 (x : Var) (H : Class) : (nb072_alpha_dummy_059 x H) ∉ (((syn_ccompl (Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb072_alpha_dummy_059] using freshVar_not_mem (((syn_ccompl (Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb072_fresh_160 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_128 A B R S_cls H) ∉ (((syn_ccompl (Class.cab (nb072_alpha_dummy_124 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_124 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H) (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb072_alpha_dummy_128] using freshVar_not_mem (((syn_ccompl (Class.cab (nb072_alpha_dummy_124 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_124 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H) (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb072_fresh_161 (y : Var) (H : Class) : (nb072_alpha_dummy_129 y H) ∉ (((syn_ccompl (Class.cab (nb072_alpha_dummy_126 y H) (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_126 y H) (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv (nb072_alpha_dummy_117 y H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb072_alpha_dummy_129] using freshVar_not_mem (((syn_ccompl (Class.cab (nb072_alpha_dummy_126 y H) (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_126 y H) (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv (nb072_alpha_dummy_117 y H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb072_fresh_162 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_026 A B R S_cls H) ∉ (((syn_ccompl (Class.cv (nb072_alpha_dummy_017 A B R S_cls H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv) := by
  simpa only [nb072_alpha_dummy_026] using freshVar_not_mem (((syn_ccompl (Class.cv (nb072_alpha_dummy_017 A B R S_cls H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv) 0

theorem nb072_fresh_163 (x : Var) (y : Var) : (nb072_alpha_dummy_027 x y) ∉ (((syn_ccompl (Class.cv (nb072_alpha_dummy_020 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_021 x y)))).fv) := by
  simpa only [nb072_alpha_dummy_027] using freshVar_not_mem (((syn_ccompl (Class.cv (nb072_alpha_dummy_020 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_021 x y)))).fv) 0

theorem nb072_fresh_164 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_078 A B R S_cls H) ∉ (((syn_ccompl (Class.cv (nb072_alpha_dummy_069 A B R S_cls H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv) := by
  simpa only [nb072_alpha_dummy_078] using freshVar_not_mem (((syn_ccompl (Class.cv (nb072_alpha_dummy_069 A B R S_cls H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv) 0

theorem nb072_fresh_165 (x : Var) (H : Class) : (nb072_alpha_dummy_079 x H) ∉ (((syn_ccompl (Class.cv (nb072_alpha_dummy_072 x H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_073 x H)))).fv) := by
  simpa only [nb072_alpha_dummy_079] using freshVar_not_mem (((syn_ccompl (Class.cv (nb072_alpha_dummy_072 x H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_073 x H)))).fv) 0

theorem nb072_fresh_166 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_108 A B R S_cls H) ∉ (((syn_ccompl (Class.cv (nb072_alpha_dummy_099 A B R S_cls H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv) := by
  simpa only [nb072_alpha_dummy_108] using freshVar_not_mem (((syn_ccompl (Class.cv (nb072_alpha_dummy_099 A B R S_cls H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv) 0

theorem nb072_fresh_167 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_109 x y H) ∉ (((syn_ccompl (Class.cv (nb072_alpha_dummy_102 x y H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_103 x y H)))).fv) := by
  simpa only [nb072_alpha_dummy_109] using freshVar_not_mem (((syn_ccompl (Class.cv (nb072_alpha_dummy_102 x y H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_103 x y H)))).fv) 0

theorem nb072_fresh_168 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_148 A B R S_cls H) ∉ (((syn_ccompl (Class.cv (nb072_alpha_dummy_139 A B R S_cls H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv) := by
  simpa only [nb072_alpha_dummy_148] using freshVar_not_mem (((syn_ccompl (Class.cv (nb072_alpha_dummy_139 A B R S_cls H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv) 0

theorem nb072_fresh_169 (y : Var) (H : Class) : (nb072_alpha_dummy_149 y H) ∉ (((syn_ccompl (Class.cv (nb072_alpha_dummy_142 y H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_143 y H)))).fv) := by
  simpa only [nb072_alpha_dummy_149] using freshVar_not_mem (((syn_ccompl (Class.cv (nb072_alpha_dummy_142 y H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_143 y H)))).fv) 0

theorem nb072_fresh_170 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_034 A B R S_cls H) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb072_alpha_dummy_034] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb072_fresh_171 (x : Var) (y : Var) : (nb072_alpha_dummy_035 x y) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb072_alpha_dummy_035] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb072_fresh_172 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_162 A B R S_cls H) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb072_alpha_dummy_162] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb072_fresh_173 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_163 x y H) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb072_alpha_dummy_163] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb072_fresh_174 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_086 A B R S_cls H) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb072_alpha_dummy_086] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb072_fresh_175 (x : Var) (H : Class) : (nb072_alpha_dummy_087 x H) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb072_alpha_dummy_087] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb072_fresh_176 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_156 A B R S_cls H) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb072_alpha_dummy_156] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb072_fresh_177 (y : Var) (H : Class) : (nb072_alpha_dummy_157 y H) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb072_alpha_dummy_157] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb072_fresh_178 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_038 A B R S_cls H) ∉ (((syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))).fv ∪ ((syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))).fv) := by
  simpa only [nb072_alpha_dummy_038] using freshVar_not_mem (((syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))).fv ∪ ((syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))).fv) 0

theorem nb072_fresh_179 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_039 A B R S_cls H) ∉ (((syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))).fv ∪ ((syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))).fv) := by
  simpa only [nb072_alpha_dummy_039] using freshVar_not_mem (((syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))).fv ∪ ((syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))).fv) 1

theorem nb072_distinct_180 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_038 A B R S_cls H) ≠ (nb072_alpha_dummy_039 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_038, nb072_alpha_dummy_039] using
    (freshVar_injective (((syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))).fv ∪ ((syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_181 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_040 x y H) ∉ (((syn_cfv H (Class.cv x))).fv ∪ ((syn_cfv H (Class.cv y))).fv) := by
  simpa only [nb072_alpha_dummy_040] using freshVar_not_mem (((syn_cfv H (Class.cv x))).fv ∪ ((syn_cfv H (Class.cv y))).fv) 0

theorem nb072_fresh_182 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_041 x y H) ∉ (((syn_cfv H (Class.cv x))).fv ∪ ((syn_cfv H (Class.cv y))).fv) := by
  simpa only [nb072_alpha_dummy_041] using freshVar_not_mem (((syn_cfv H (Class.cv x))).fv ∪ ((syn_cfv H (Class.cv y))).fv) 1

theorem nb072_distinct_183 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_040 x y H) ≠ (nb072_alpha_dummy_041 x y H) := by
  simpa only [nb072_alpha_dummy_040, nb072_alpha_dummy_041] using
    (freshVar_injective (((syn_cfv H (Class.cv x))).fv ∪ ((syn_cfv H (Class.cv y))).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_184 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_022 A B R S_cls H) ∉ (((syn_cnin (Class.cv (nb072_alpha_dummy_017 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_017 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv) := by
  simpa only [nb072_alpha_dummy_022] using freshVar_not_mem (((syn_cnin (Class.cv (nb072_alpha_dummy_017 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_017 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv) 0

theorem nb072_fresh_185 (x : Var) (y : Var) : (nb072_alpha_dummy_023 x y) ∉ (((syn_cnin (Class.cv (nb072_alpha_dummy_020 x y)) (Class.cv (nb072_alpha_dummy_021 x y)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_020 x y)) (Class.cv (nb072_alpha_dummy_021 x y)))).fv) := by
  simpa only [nb072_alpha_dummy_023] using freshVar_not_mem (((syn_cnin (Class.cv (nb072_alpha_dummy_020 x y)) (Class.cv (nb072_alpha_dummy_021 x y)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_020 x y)) (Class.cv (nb072_alpha_dummy_021 x y)))).fv) 0

theorem nb072_fresh_186 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_074 A B R S_cls H) ∉ (((syn_cnin (Class.cv (nb072_alpha_dummy_069 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_069 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv) := by
  simpa only [nb072_alpha_dummy_074] using freshVar_not_mem (((syn_cnin (Class.cv (nb072_alpha_dummy_069 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_069 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv) 0

theorem nb072_fresh_187 (x : Var) (H : Class) : (nb072_alpha_dummy_075 x H) ∉ (((syn_cnin (Class.cv (nb072_alpha_dummy_072 x H)) (Class.cv (nb072_alpha_dummy_073 x H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_072 x H)) (Class.cv (nb072_alpha_dummy_073 x H)))).fv) := by
  simpa only [nb072_alpha_dummy_075] using freshVar_not_mem (((syn_cnin (Class.cv (nb072_alpha_dummy_072 x H)) (Class.cv (nb072_alpha_dummy_073 x H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_072 x H)) (Class.cv (nb072_alpha_dummy_073 x H)))).fv) 0

theorem nb072_fresh_188 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_104 A B R S_cls H) ∉ (((syn_cnin (Class.cv (nb072_alpha_dummy_099 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_099 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv) := by
  simpa only [nb072_alpha_dummy_104] using freshVar_not_mem (((syn_cnin (Class.cv (nb072_alpha_dummy_099 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_099 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv) 0

theorem nb072_fresh_189 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_105 x y H) ∉ (((syn_cnin (Class.cv (nb072_alpha_dummy_102 x y H)) (Class.cv (nb072_alpha_dummy_103 x y H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_102 x y H)) (Class.cv (nb072_alpha_dummy_103 x y H)))).fv) := by
  simpa only [nb072_alpha_dummy_105] using freshVar_not_mem (((syn_cnin (Class.cv (nb072_alpha_dummy_102 x y H)) (Class.cv (nb072_alpha_dummy_103 x y H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_102 x y H)) (Class.cv (nb072_alpha_dummy_103 x y H)))).fv) 0

theorem nb072_fresh_190 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_144 A B R S_cls H) ∉ (((syn_cnin (Class.cv (nb072_alpha_dummy_139 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_139 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv) := by
  simpa only [nb072_alpha_dummy_144] using freshVar_not_mem (((syn_cnin (Class.cv (nb072_alpha_dummy_139 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_139 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv) 0

theorem nb072_fresh_191 (y : Var) (H : Class) : (nb072_alpha_dummy_145 y H) ∉ (((syn_cnin (Class.cv (nb072_alpha_dummy_142 y H)) (Class.cv (nb072_alpha_dummy_143 y H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_142 y H)) (Class.cv (nb072_alpha_dummy_143 y H)))).fv) := by
  simpa only [nb072_alpha_dummy_145] using freshVar_not_mem (((syn_cnin (Class.cv (nb072_alpha_dummy_142 y H)) (Class.cv (nb072_alpha_dummy_143 y H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_142 y H)) (Class.cv (nb072_alpha_dummy_143 y H)))).fv) 0

theorem nb072_fresh_192 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_036 A B R S_cls H) ∉ (((syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))).fv) := by
  simpa only [nb072_alpha_dummy_036] using freshVar_not_mem (((syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))).fv) 0

theorem nb072_fresh_193 (x : Var) (y : Var) : (nb072_alpha_dummy_037 x y) ∉ (((syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))).fv) := by
  simpa only [nb072_alpha_dummy_037] using freshVar_not_mem (((syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))).fv) 0

theorem nb072_fresh_194 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_164 A B R S_cls H) ∉ (((syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))).fv) := by
  simpa only [nb072_alpha_dummy_164] using freshVar_not_mem (((syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))).fv) 0

theorem nb072_fresh_195 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_165 x y H) ∉ (((syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))).fv) := by
  simpa only [nb072_alpha_dummy_165] using freshVar_not_mem (((syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))).fv) 0

theorem nb072_fresh_196 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_088 A B R S_cls H) ∉ (((syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))).fv) := by
  simpa only [nb072_alpha_dummy_088] using freshVar_not_mem (((syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))).fv) 0

theorem nb072_fresh_197 (x : Var) (H : Class) : (nb072_alpha_dummy_089 x H) ∉ (((syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))).fv) := by
  simpa only [nb072_alpha_dummy_089] using freshVar_not_mem (((syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))).fv) 0

theorem nb072_fresh_198 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_158 A B R S_cls H) ∉ (((syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))).fv) := by
  simpa only [nb072_alpha_dummy_158] using freshVar_not_mem (((syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))).fv) 0

theorem nb072_fresh_199 (y : Var) (H : Class) : (nb072_alpha_dummy_159 y H) ∉ (((syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))).fv) := by
  simpa only [nb072_alpha_dummy_159] using freshVar_not_mem (((syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))).fv) 0

theorem nb072_fresh_200 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_046 A B R S_cls H) ∉ ((H).fv ∪ ((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_046] using freshVar_not_mem ((H).fv ∪ ((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv) 0

theorem nb072_fresh_201 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_116 A B R S_cls H) ∉ ((H).fv ∪ ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) := by
  simpa only [nb072_alpha_dummy_116] using freshVar_not_mem ((H).fv ∪ ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) 0

theorem nb072_fresh_202 (x : Var) (H : Class) : (nb072_alpha_dummy_047 x H) ∉ ((H).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb072_alpha_dummy_047] using freshVar_not_mem ((H).fv ∪ ((Class.cv x)).fv) 0

theorem nb072_fresh_203 (y : Var) (H : Class) : (nb072_alpha_dummy_117 y H) ∉ ((H).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb072_alpha_dummy_117] using freshVar_not_mem ((H).fv ∪ ((Class.cv y)).fv) 0

theorem nb072_fresh_204 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_000 A B R S_cls H) ∉ ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) := by
  simpa only [nb072_alpha_dummy_000] using freshVar_not_mem ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 0

theorem nb072_fresh_205 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_001 A B R S_cls H) ∉ ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) := by
  simpa only [nb072_alpha_dummy_001] using freshVar_not_mem ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 1

theorem nb072_distinct_206 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_000 A B R S_cls H) ≠ (nb072_alpha_dummy_001 A B R S_cls H) := by
  simpa only [nb072_alpha_dummy_000, nb072_alpha_dummy_001] using
    (freshVar_injective ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) (i := 0) (j := 1) (by decide))

theorem nb072_fresh_207 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_048 A B R S_cls H) ∉ (({(nb072_alpha_dummy_046 A B R S_cls H)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)))).fv) := by
  simpa only [nb072_alpha_dummy_048] using freshVar_not_mem (({(nb072_alpha_dummy_046 A B R S_cls H)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)))).fv) 0

theorem nb072_fresh_208 (x : Var) (H : Class) : (nb072_alpha_dummy_049 x H) ∉ (({(nb072_alpha_dummy_047 x H)} : Finset Var) ∪ ((syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H)))).fv) := by
  simpa only [nb072_alpha_dummy_049] using freshVar_not_mem (({(nb072_alpha_dummy_047 x H)} : Finset Var) ∪ ((syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H)))).fv) 0

theorem nb072_fresh_209 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_118 A B R S_cls H) ∉ (({(nb072_alpha_dummy_116 A B R S_cls H)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)))).fv) := by
  simpa only [nb072_alpha_dummy_118] using freshVar_not_mem (({(nb072_alpha_dummy_116 A B R S_cls H)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)))).fv) 0

theorem nb072_fresh_210 (y : Var) (H : Class) : (nb072_alpha_dummy_119 y H) ∉ (({(nb072_alpha_dummy_117 y H)} : Finset Var) ∪ ((syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H)))).fv) := by
  simpa only [nb072_alpha_dummy_119] using freshVar_not_mem (({(nb072_alpha_dummy_117 y H)} : Finset Var) ∪ ((syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H)))).fv) 0

theorem nb072_support_mem_0000 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_000 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0001 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_000 A B R S_cls H) ∈ (((syn_ccompl (Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0000 A B R S_cls H) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0000 A B R S_cls H) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0002 (x : Var) (y : Var) : x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0003 (x : Var) (y : Var) : x ∈ (((syn_ccompl (Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0002 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0002 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0004 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_000 A B R S_cls H) ∈ (((Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0000 A B R S_cls H) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0000 A B R S_cls H) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0005 (x : Var) (y : Var) : x ∈ (((Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0002 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0002 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0006 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_003 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_003 A B R S_cls H))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0007 (x : Var) (y : Var) : (nb072_alpha_dummy_005 x y) ∈ (((Class.cv (nb072_alpha_dummy_005 x y))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0008 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_010 A B R S_cls H) ∈ (((Wff.classMem (Class.cv (nb072_alpha_dummy_010 A B R S_cls H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_010 A B R S_cls H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0009 (x : Var) (y : Var) : (nb072_alpha_dummy_012 x y) ∈ (((Wff.classMem (Class.cv (nb072_alpha_dummy_012 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_012 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_012 x y))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0010 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_010 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0011 (x : Var) (y : Var) : (nb072_alpha_dummy_012 x y) ∈ (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0012 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_017 A B R S_cls H) ∈ (((syn_cnin (Class.cv (nb072_alpha_dummy_017 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_017 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0013 (x : Var) (y : Var) : (nb072_alpha_dummy_020 x y) ∈ (((syn_cnin (Class.cv (nb072_alpha_dummy_020 x y)) (Class.cv (nb072_alpha_dummy_021 x y)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_020 x y)) (Class.cv (nb072_alpha_dummy_021 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0014 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_017 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0015 (x : Var) (y : Var) : (nb072_alpha_dummy_020 x y) ∈ (((Class.cv (nb072_alpha_dummy_020 x y))).fv ∪ ((Class.cv (nb072_alpha_dummy_021 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0016 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_018 A B R S_cls H) ∈ (((syn_cnin (Class.cv (nb072_alpha_dummy_017 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_017 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0017 (x : Var) (y : Var) : (nb072_alpha_dummy_021 x y) ∈ (((syn_cnin (Class.cv (nb072_alpha_dummy_020 x y)) (Class.cv (nb072_alpha_dummy_021 x y)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_020 x y)) (Class.cv (nb072_alpha_dummy_021 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0018 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_018 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0019 (x : Var) (y : Var) : (nb072_alpha_dummy_021 x y) ∈ (((Class.cv (nb072_alpha_dummy_020 x y))).fv ∪ ((Class.cv (nb072_alpha_dummy_021 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0020 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_017 A B R S_cls H) ∈ (((syn_ccompl (Class.cv (nb072_alpha_dummy_017 A B R S_cls H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0021 (x : Var) (y : Var) : (nb072_alpha_dummy_020 x y) ∈ (((syn_ccompl (Class.cv (nb072_alpha_dummy_020 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_021 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0022 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_017 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0023 (x : Var) (y : Var) : (nb072_alpha_dummy_020 x y) ∈ (((Class.cv (nb072_alpha_dummy_020 x y))).fv ∪ ((Class.cv (nb072_alpha_dummy_020 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0024 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_018 A B R S_cls H) ∈ (((syn_ccompl (Class.cv (nb072_alpha_dummy_017 A B R S_cls H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0025 (x : Var) (y : Var) : (nb072_alpha_dummy_021 x y) ∈ (((syn_ccompl (Class.cv (nb072_alpha_dummy_020 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_021 x y)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0026 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_018 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0027 (x : Var) (y : Var) : (nb072_alpha_dummy_021 x y) ∈ (((Class.cv (nb072_alpha_dummy_021 x y))).fv ∪ ((Class.cv (nb072_alpha_dummy_021 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0028 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_001 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
