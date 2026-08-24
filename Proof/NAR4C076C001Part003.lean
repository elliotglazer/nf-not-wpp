import NAR4C076C001Part002

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

theorem nb076_fresh_141 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_094 g a b) ∉ (((Wff.classMem (Class.cv (nb076_alpha_dummy_091 g a b)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_091 g a b)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_091 g a b))).fv) := by
  simpa only [nb076_alpha_dummy_094] using freshVar_not_mem (((Wff.classMem (Class.cv (nb076_alpha_dummy_091 g a b)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_091 g a b)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_091 g a b))).fv) 0

theorem nb076_fresh_142 : (nb076_alpha_dummy_131) ∉ (((Wff.classMem (Class.cv (nb076_alpha_dummy_127)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_127)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_127))).fv) := by
  simpa only [nb076_alpha_dummy_131] using freshVar_not_mem (((Wff.classMem (Class.cv (nb076_alpha_dummy_127)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_127)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_127))).fv) 0

theorem nb076_fresh_143 (g : Var) (b : Var) : (nb076_alpha_dummy_132 g b) ∉ (((Wff.classMem (Class.cv (nb076_alpha_dummy_129 g b)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_129 g b)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_129 g b))).fv) := by
  simpa only [nb076_alpha_dummy_132] using freshVar_not_mem (((Wff.classMem (Class.cv (nb076_alpha_dummy_129 g b)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_129 g b)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_129 g b))).fv) 0

theorem nb076_fresh_144 : (nb076_alpha_dummy_013) ∉ (((syn_ccompl (Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004))) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cphi (Class.cv (nb076_alpha_dummy_010)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005)) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb076_alpha_dummy_013] using freshVar_not_mem (((syn_ccompl (Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004))) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cphi (Class.cv (nb076_alpha_dummy_010)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005)) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb076_fresh_145 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_014 g m n a b) ∉ (((syn_ccompl (Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb076_alpha_dummy_014] using freshVar_not_mem (((syn_ccompl (Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb076_fresh_146 : (nb076_alpha_dummy_021) ∉ (((syn_ccompl (Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cphi (Class.cv (nb076_alpha_dummy_018)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb076_alpha_dummy_021] using freshVar_not_mem (((syn_ccompl (Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cphi (Class.cv (nb076_alpha_dummy_018)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb076_fresh_147 (m : Var) (n : Var) : (nb076_alpha_dummy_022 m n) ∉ (((syn_ccompl (Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb076_alpha_dummy_022] using freshVar_not_mem (((syn_ccompl (Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb076_fresh_148 : (nb076_alpha_dummy_085) ∉ (((syn_ccompl (Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000)) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cphi (Class.cv (nb076_alpha_dummy_082)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002))) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb076_alpha_dummy_085] using freshVar_not_mem (((syn_ccompl (Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000)) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cphi (Class.cv (nb076_alpha_dummy_082)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002))) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb076_fresh_149 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_086 g a b) ∉ (((syn_ccompl (Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g)) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb076_alpha_dummy_086] using freshVar_not_mem (((syn_ccompl (Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g)) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb076_fresh_150 : (nb076_alpha_dummy_123) ∉ (((syn_ccompl (Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cphi (Class.cv (nb076_alpha_dummy_120)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb076_alpha_dummy_123] using freshVar_not_mem (((syn_ccompl (Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cphi (Class.cv (nb076_alpha_dummy_120)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb076_fresh_151 (g : Var) (b : Var) : (nb076_alpha_dummy_124 g b) ∉ (((syn_ccompl (Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb076_alpha_dummy_124] using freshVar_not_mem (((syn_ccompl (Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb076_fresh_152 : (nb076_alpha_dummy_041) ∉ (((syn_ccompl (Class.cv (nb076_alpha_dummy_032)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_033)))).fv) := by
  simpa only [nb076_alpha_dummy_041] using freshVar_not_mem (((syn_ccompl (Class.cv (nb076_alpha_dummy_032)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_033)))).fv) 0

theorem nb076_fresh_153 (m : Var) (n : Var) : (nb076_alpha_dummy_042 m n) ∉ (((syn_ccompl (Class.cv (nb076_alpha_dummy_035 m n)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_036 m n)))).fv) := by
  simpa only [nb076_alpha_dummy_042] using freshVar_not_mem (((syn_ccompl (Class.cv (nb076_alpha_dummy_035 m n)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_036 m n)))).fv) 0

theorem nb076_fresh_154 : (nb076_alpha_dummy_069) ∉ (((syn_ccompl (Class.cv (nb076_alpha_dummy_060)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_061)))).fv) := by
  simpa only [nb076_alpha_dummy_069] using freshVar_not_mem (((syn_ccompl (Class.cv (nb076_alpha_dummy_060)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_061)))).fv) 0

theorem nb076_fresh_155 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_070 g m n a b) ∉ (((syn_ccompl (Class.cv (nb076_alpha_dummy_063 g m n a b)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv) := by
  simpa only [nb076_alpha_dummy_070] using freshVar_not_mem (((syn_ccompl (Class.cv (nb076_alpha_dummy_063 g m n a b)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv) 0

theorem nb076_fresh_156 : (nb076_alpha_dummy_105) ∉ (((syn_ccompl (Class.cv (nb076_alpha_dummy_096)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_097)))).fv) := by
  simpa only [nb076_alpha_dummy_105] using freshVar_not_mem (((syn_ccompl (Class.cv (nb076_alpha_dummy_096)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_097)))).fv) 0

theorem nb076_fresh_157 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_106 g a b) ∉ (((syn_ccompl (Class.cv (nb076_alpha_dummy_099 g a b)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_100 g a b)))).fv) := by
  simpa only [nb076_alpha_dummy_106] using freshVar_not_mem (((syn_ccompl (Class.cv (nb076_alpha_dummy_099 g a b)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_100 g a b)))).fv) 0

theorem nb076_fresh_158 : (nb076_alpha_dummy_143) ∉ (((syn_ccompl (Class.cv (nb076_alpha_dummy_134)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_135)))).fv) := by
  simpa only [nb076_alpha_dummy_143] using freshVar_not_mem (((syn_ccompl (Class.cv (nb076_alpha_dummy_134)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_135)))).fv) 0

theorem nb076_fresh_159 (g : Var) (b : Var) : (nb076_alpha_dummy_144 g b) ∉ (((syn_ccompl (Class.cv (nb076_alpha_dummy_137 g b)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_138 g b)))).fv) := by
  simpa only [nb076_alpha_dummy_144] using freshVar_not_mem (((syn_ccompl (Class.cv (nb076_alpha_dummy_137 g b)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_138 g b)))).fv) 0

theorem nb076_fresh_160 : (nb076_alpha_dummy_077) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_010))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb076_alpha_dummy_077] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_010))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb076_fresh_161 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_078 g m n a b) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb076_alpha_dummy_078] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb076_fresh_162 : (nb076_alpha_dummy_049) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_018))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb076_alpha_dummy_049] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_018))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb076_fresh_163 (m : Var) (n : Var) : (nb076_alpha_dummy_050 m n) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb076_alpha_dummy_050] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb076_fresh_164 : (nb076_alpha_dummy_155) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_082))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb076_alpha_dummy_155] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_082))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb076_fresh_165 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_156 g a b) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb076_alpha_dummy_156] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb076_fresh_166 : (nb076_alpha_dummy_151) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_120))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb076_alpha_dummy_151] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_120))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb076_fresh_167 (g : Var) (b : Var) : (nb076_alpha_dummy_152 g b) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb076_alpha_dummy_152] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb076_fresh_168 : (nb076_alpha_dummy_037) ∉ (((syn_cnin (Class.cv (nb076_alpha_dummy_032)) (Class.cv (nb076_alpha_dummy_033)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_032)) (Class.cv (nb076_alpha_dummy_033)))).fv) := by
  simpa only [nb076_alpha_dummy_037] using freshVar_not_mem (((syn_cnin (Class.cv (nb076_alpha_dummy_032)) (Class.cv (nb076_alpha_dummy_033)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_032)) (Class.cv (nb076_alpha_dummy_033)))).fv) 0

theorem nb076_fresh_169 (m : Var) (n : Var) : (nb076_alpha_dummy_038 m n) ∉ (((syn_cnin (Class.cv (nb076_alpha_dummy_035 m n)) (Class.cv (nb076_alpha_dummy_036 m n)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_035 m n)) (Class.cv (nb076_alpha_dummy_036 m n)))).fv) := by
  simpa only [nb076_alpha_dummy_038] using freshVar_not_mem (((syn_cnin (Class.cv (nb076_alpha_dummy_035 m n)) (Class.cv (nb076_alpha_dummy_036 m n)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_035 m n)) (Class.cv (nb076_alpha_dummy_036 m n)))).fv) 0

theorem nb076_fresh_170 : (nb076_alpha_dummy_065) ∉ (((syn_cnin (Class.cv (nb076_alpha_dummy_060)) (Class.cv (nb076_alpha_dummy_061)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_060)) (Class.cv (nb076_alpha_dummy_061)))).fv) := by
  simpa only [nb076_alpha_dummy_065] using freshVar_not_mem (((syn_cnin (Class.cv (nb076_alpha_dummy_060)) (Class.cv (nb076_alpha_dummy_061)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_060)) (Class.cv (nb076_alpha_dummy_061)))).fv) 0

theorem nb076_fresh_171 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_066 g m n a b) ∉ (((syn_cnin (Class.cv (nb076_alpha_dummy_063 g m n a b)) (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_063 g m n a b)) (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv) := by
  simpa only [nb076_alpha_dummy_066] using freshVar_not_mem (((syn_cnin (Class.cv (nb076_alpha_dummy_063 g m n a b)) (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_063 g m n a b)) (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv) 0

theorem nb076_fresh_172 : (nb076_alpha_dummy_101) ∉ (((syn_cnin (Class.cv (nb076_alpha_dummy_096)) (Class.cv (nb076_alpha_dummy_097)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_096)) (Class.cv (nb076_alpha_dummy_097)))).fv) := by
  simpa only [nb076_alpha_dummy_101] using freshVar_not_mem (((syn_cnin (Class.cv (nb076_alpha_dummy_096)) (Class.cv (nb076_alpha_dummy_097)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_096)) (Class.cv (nb076_alpha_dummy_097)))).fv) 0

theorem nb076_fresh_173 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_102 g a b) ∉ (((syn_cnin (Class.cv (nb076_alpha_dummy_099 g a b)) (Class.cv (nb076_alpha_dummy_100 g a b)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_099 g a b)) (Class.cv (nb076_alpha_dummy_100 g a b)))).fv) := by
  simpa only [nb076_alpha_dummy_102] using freshVar_not_mem (((syn_cnin (Class.cv (nb076_alpha_dummy_099 g a b)) (Class.cv (nb076_alpha_dummy_100 g a b)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_099 g a b)) (Class.cv (nb076_alpha_dummy_100 g a b)))).fv) 0

theorem nb076_fresh_174 : (nb076_alpha_dummy_139) ∉ (((syn_cnin (Class.cv (nb076_alpha_dummy_134)) (Class.cv (nb076_alpha_dummy_135)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_134)) (Class.cv (nb076_alpha_dummy_135)))).fv) := by
  simpa only [nb076_alpha_dummy_139] using freshVar_not_mem (((syn_cnin (Class.cv (nb076_alpha_dummy_134)) (Class.cv (nb076_alpha_dummy_135)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_134)) (Class.cv (nb076_alpha_dummy_135)))).fv) 0

theorem nb076_fresh_175 (g : Var) (b : Var) : (nb076_alpha_dummy_140 g b) ∉ (((syn_cnin (Class.cv (nb076_alpha_dummy_137 g b)) (Class.cv (nb076_alpha_dummy_138 g b)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_137 g b)) (Class.cv (nb076_alpha_dummy_138 g b)))).fv) := by
  simpa only [nb076_alpha_dummy_140] using freshVar_not_mem (((syn_cnin (Class.cv (nb076_alpha_dummy_137 g b)) (Class.cv (nb076_alpha_dummy_138 g b)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_137 g b)) (Class.cv (nb076_alpha_dummy_138 g b)))).fv) 0

theorem nb076_fresh_176 : (nb076_alpha_dummy_009) ∉ (((syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))).fv ∪ ((Class.cv (nb076_alpha_dummy_005))).fv) := by
  simpa only [nb076_alpha_dummy_009] using freshVar_not_mem (((syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))).fv ∪ ((Class.cv (nb076_alpha_dummy_005))).fv) 0

theorem nb076_fresh_177 : (nb076_alpha_dummy_010) ∉ (((syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))).fv ∪ ((Class.cv (nb076_alpha_dummy_005))).fv) := by
  simpa only [nb076_alpha_dummy_010] using freshVar_not_mem (((syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))).fv ∪ ((Class.cv (nb076_alpha_dummy_005))).fv) 1

theorem nb076_distinct_178 : (nb076_alpha_dummy_009) ≠ (nb076_alpha_dummy_010) := by
  simpa only [nb076_alpha_dummy_009, nb076_alpha_dummy_010] using
    (freshVar_injective (((syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))).fv ∪ ((Class.cv (nb076_alpha_dummy_005))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_179 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_011 g m n a b) ∉ (((syn_cop (Class.cv m) (Class.cv n))).fv ∪ ((Class.cv (nb076_alpha_dummy_006 g m n a b))).fv) := by
  simpa only [nb076_alpha_dummy_011] using freshVar_not_mem (((syn_cop (Class.cv m) (Class.cv n))).fv ∪ ((Class.cv (nb076_alpha_dummy_006 g m n a b))).fv) 0

theorem nb076_fresh_180 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_012 g m n a b) ∉ (((syn_cop (Class.cv m) (Class.cv n))).fv ∪ ((Class.cv (nb076_alpha_dummy_006 g m n a b))).fv) := by
  simpa only [nb076_alpha_dummy_012] using freshVar_not_mem (((syn_cop (Class.cv m) (Class.cv n))).fv ∪ ((Class.cv (nb076_alpha_dummy_006 g m n a b))).fv) 1

theorem nb076_distinct_181 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_011 g m n a b) ≠ (nb076_alpha_dummy_012 g m n a b) := by
  simpa only [nb076_alpha_dummy_011, nb076_alpha_dummy_012] using
    (freshVar_injective (((syn_cop (Class.cv m) (Class.cv n))).fv ∪ ((Class.cv (nb076_alpha_dummy_006 g m n a b))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_182 : (nb076_alpha_dummy_079) ∉ (((syn_cphi (Class.cv (nb076_alpha_dummy_010)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_010)))).fv) := by
  simpa only [nb076_alpha_dummy_079] using freshVar_not_mem (((syn_cphi (Class.cv (nb076_alpha_dummy_010)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_010)))).fv) 0

theorem nb076_fresh_183 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_080 g m n a b) ∉ (((syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))).fv) := by
  simpa only [nb076_alpha_dummy_080] using freshVar_not_mem (((syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))).fv) 0

theorem nb076_fresh_184 : (nb076_alpha_dummy_051) ∉ (((syn_cphi (Class.cv (nb076_alpha_dummy_018)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_018)))).fv) := by
  simpa only [nb076_alpha_dummy_051] using freshVar_not_mem (((syn_cphi (Class.cv (nb076_alpha_dummy_018)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_018)))).fv) 0

theorem nb076_fresh_185 (m : Var) (n : Var) : (nb076_alpha_dummy_052 m n) ∉ (((syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))).fv) := by
  simpa only [nb076_alpha_dummy_052] using freshVar_not_mem (((syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))).fv) 0

theorem nb076_fresh_186 : (nb076_alpha_dummy_157) ∉ (((syn_cphi (Class.cv (nb076_alpha_dummy_082)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_082)))).fv) := by
  simpa only [nb076_alpha_dummy_157] using freshVar_not_mem (((syn_cphi (Class.cv (nb076_alpha_dummy_082)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_082)))).fv) 0

theorem nb076_fresh_187 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_158 g a b) ∉ (((syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))).fv) := by
  simpa only [nb076_alpha_dummy_158] using freshVar_not_mem (((syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))).fv) 0

theorem nb076_fresh_188 : (nb076_alpha_dummy_153) ∉ (((syn_cphi (Class.cv (nb076_alpha_dummy_120)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_120)))).fv) := by
  simpa only [nb076_alpha_dummy_153] using freshVar_not_mem (((syn_cphi (Class.cv (nb076_alpha_dummy_120)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_120)))).fv) 0

theorem nb076_fresh_189 (g : Var) (b : Var) : (nb076_alpha_dummy_154 g b) ∉ (((syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))).fv) := by
  simpa only [nb076_alpha_dummy_154] using freshVar_not_mem (((syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))).fv) 0

theorem nb076_fresh_190 : (nb076_alpha_dummy_005) ∉ (({(nb076_alpha_dummy_003)} : Finset Var) ∪ ((syn_cncs)).fv ∪ ({(nb076_alpha_dummy_004)} : Finset Var) ∪ ((syn_cncs)).fv ∪ ((Class.cab (nb076_alpha_dummy_000) (syn_wrex (nb076_alpha_dummy_001) (Class.cv (nb076_alpha_dummy_003)) (syn_wrex (nb076_alpha_dummy_002) (Class.cv (nb076_alpha_dummy_004)) (syn_wbr (Class.cv (nb076_alpha_dummy_000)) (syn_cen) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))))))).fv) := by
  simpa only [nb076_alpha_dummy_005] using freshVar_not_mem (({(nb076_alpha_dummy_003)} : Finset Var) ∪ ((syn_cncs)).fv ∪ ({(nb076_alpha_dummy_004)} : Finset Var) ∪ ((syn_cncs)).fv ∪ ((Class.cab (nb076_alpha_dummy_000) (syn_wrex (nb076_alpha_dummy_001) (Class.cv (nb076_alpha_dummy_003)) (syn_wrex (nb076_alpha_dummy_002) (Class.cv (nb076_alpha_dummy_004)) (syn_wbr (Class.cv (nb076_alpha_dummy_000)) (syn_cen) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))))))).fv) 0

theorem nb076_fresh_191 : (nb076_alpha_dummy_007) ∉ (({(nb076_alpha_dummy_003)} : Finset Var) ∪ ({(nb076_alpha_dummy_004)} : Finset Var) ∪ ({(nb076_alpha_dummy_005)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_003)) (syn_cncs)) (Wff.classMem (Class.cv (nb076_alpha_dummy_004)) (syn_cncs))) (Wff.classEq (Class.cv (nb076_alpha_dummy_005)) (Class.cab (nb076_alpha_dummy_000) (syn_wrex (nb076_alpha_dummy_001) (Class.cv (nb076_alpha_dummy_003)) (syn_wrex (nb076_alpha_dummy_002) (Class.cv (nb076_alpha_dummy_004)) (syn_wbr (Class.cv (nb076_alpha_dummy_000)) (syn_cen) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))))))))).fv) := by
  simpa only [nb076_alpha_dummy_007] using freshVar_not_mem (({(nb076_alpha_dummy_003)} : Finset Var) ∪ ({(nb076_alpha_dummy_004)} : Finset Var) ∪ ({(nb076_alpha_dummy_005)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_003)) (syn_cncs)) (Wff.classMem (Class.cv (nb076_alpha_dummy_004)) (syn_cncs))) (Wff.classEq (Class.cv (nb076_alpha_dummy_005)) (Class.cab (nb076_alpha_dummy_000) (syn_wrex (nb076_alpha_dummy_001) (Class.cv (nb076_alpha_dummy_003)) (syn_wrex (nb076_alpha_dummy_002) (Class.cv (nb076_alpha_dummy_004)) (syn_wbr (Class.cv (nb076_alpha_dummy_000)) (syn_cen) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))))))))).fv) 0

theorem nb076_fresh_192 : (nb076_alpha_dummy_117) ∉ (({(nb076_alpha_dummy_113)} : Finset Var) ∪ ({(nb076_alpha_dummy_114)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_113)) (Class.cv (nb076_alpha_dummy_001))) (Wff.classMem (Class.cv (nb076_alpha_dummy_114)) (Class.cv (nb076_alpha_dummy_002))))).fv) := by
  simpa only [nb076_alpha_dummy_117] using freshVar_not_mem (({(nb076_alpha_dummy_113)} : Finset Var) ∪ ({(nb076_alpha_dummy_114)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_113)) (Class.cv (nb076_alpha_dummy_001))) (Wff.classMem (Class.cv (nb076_alpha_dummy_114)) (Class.cv (nb076_alpha_dummy_002))))).fv) 0

theorem nb076_fresh_193 (g : Var) (b : Var) : (nb076_alpha_dummy_118 g b) ∉ (({(nb076_alpha_dummy_115 g b)} : Finset Var) ∪ ({(nb076_alpha_dummy_116 g b)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_115 g b)) (Class.cv b)) (Wff.classMem (Class.cv (nb076_alpha_dummy_116 g b)) (Class.cv g)))).fv) := by
  simpa only [nb076_alpha_dummy_118] using freshVar_not_mem (({(nb076_alpha_dummy_115 g b)} : Finset Var) ∪ ({(nb076_alpha_dummy_116 g b)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_115 g b)) (Class.cv b)) (Wff.classMem (Class.cv (nb076_alpha_dummy_116 g b)) (Class.cv g)))).fv) 0

theorem nb076_fresh_194 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_006 g m n a b) ∉ (({m} : Finset Var) ∪ ((syn_cncs)).fv ∪ ({n} : Finset Var) ∪ ((syn_cncs)).fv ∪ ((Class.cab a (syn_wrex b (Class.cv m) (syn_wrex g (Class.cv n) (syn_wbr (Class.cv a) (syn_cen) (syn_cxp (Class.cv b) (Class.cv g))))))).fv) := by
  simpa only [nb076_alpha_dummy_006] using freshVar_not_mem (({m} : Finset Var) ∪ ((syn_cncs)).fv ∪ ({n} : Finset Var) ∪ ((syn_cncs)).fv ∪ ((Class.cab a (syn_wrex b (Class.cv m) (syn_wrex g (Class.cv n) (syn_wbr (Class.cv a) (syn_cen) (syn_cxp (Class.cv b) (Class.cv g))))))).fv) 0

theorem nb076_fresh_195 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_008 g m n a b) ∉ (({m} : Finset Var) ∪ ({n} : Finset Var) ∪ ({(nb076_alpha_dummy_006 g m n a b)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv m) (syn_cncs)) (Wff.classMem (Class.cv n) (syn_cncs))) (Wff.classEq (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Class.cab a (syn_wrex b (Class.cv m) (syn_wrex g (Class.cv n) (syn_wbr (Class.cv a) (syn_cen) (syn_cxp (Class.cv b) (Class.cv g))))))))).fv) := by
  simpa only [nb076_alpha_dummy_008] using freshVar_not_mem (({m} : Finset Var) ∪ ({n} : Finset Var) ∪ ({(nb076_alpha_dummy_006 g m n a b)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv m) (syn_cncs)) (Wff.classMem (Class.cv n) (syn_cncs))) (Wff.classEq (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Class.cab a (syn_wrex b (Class.cv m) (syn_wrex g (Class.cv n) (syn_wbr (Class.cv a) (syn_cen) (syn_cxp (Class.cv b) (Class.cv g))))))))).fv) 0

theorem nb076_fresh_196 : (nb076_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb076_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb076_fresh_197 : (nb076_alpha_dummy_001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb076_alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb076_fresh_198 : (nb076_alpha_dummy_002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb076_alpha_dummy_002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb076_fresh_199 : (nb076_alpha_dummy_003) ∉ ((∅ : Finset Var)) := by
  simpa only [nb076_alpha_dummy_003] using freshVar_not_mem ((∅ : Finset Var)) 3

theorem nb076_fresh_200 : (nb076_alpha_dummy_004) ∉ ((∅ : Finset Var)) := by
  simpa only [nb076_alpha_dummy_004] using freshVar_not_mem ((∅ : Finset Var)) 4

theorem nb076_distinct_201 : (nb076_alpha_dummy_000) ≠ (nb076_alpha_dummy_001) := by
  simpa only [nb076_alpha_dummy_000, nb076_alpha_dummy_001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb076_distinct_202 : (nb076_alpha_dummy_000) ≠ (nb076_alpha_dummy_002) := by
  simpa only [nb076_alpha_dummy_000, nb076_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb076_distinct_203 : (nb076_alpha_dummy_000) ≠ (nb076_alpha_dummy_003) := by
  simpa only [nb076_alpha_dummy_000, nb076_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 3) (by decide))

theorem nb076_distinct_204 : (nb076_alpha_dummy_000) ≠ (nb076_alpha_dummy_004) := by
  simpa only [nb076_alpha_dummy_000, nb076_alpha_dummy_004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 4) (by decide))

theorem nb076_distinct_205 : (nb076_alpha_dummy_001) ≠ (nb076_alpha_dummy_002) := by
  simpa only [nb076_alpha_dummy_001, nb076_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb076_distinct_206 : (nb076_alpha_dummy_001) ≠ (nb076_alpha_dummy_003) := by
  simpa only [nb076_alpha_dummy_001, nb076_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 3) (by decide))

theorem nb076_distinct_207 : (nb076_alpha_dummy_001) ≠ (nb076_alpha_dummy_004) := by
  simpa only [nb076_alpha_dummy_001, nb076_alpha_dummy_004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 4) (by decide))

theorem nb076_distinct_208 : (nb076_alpha_dummy_002) ≠ (nb076_alpha_dummy_003) := by
  simpa only [nb076_alpha_dummy_002, nb076_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 3) (by decide))

theorem nb076_distinct_209 : (nb076_alpha_dummy_002) ≠ (nb076_alpha_dummy_004) := by
  simpa only [nb076_alpha_dummy_002, nb076_alpha_dummy_004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 4) (by decide))

theorem nb076_distinct_210 : (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_004) := by
  simpa only [nb076_alpha_dummy_003, nb076_alpha_dummy_004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 3) (j := 4) (by decide))

theorem nb076_support_mem_0000 : (nb076_alpha_dummy_003) ∈ (({(nb076_alpha_dummy_003)} : Finset Var) ∪ ({(nb076_alpha_dummy_004)} : Finset Var) ∪ ({(nb076_alpha_dummy_005)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_003)) (syn_cncs)) (Wff.classMem (Class.cv (nb076_alpha_dummy_004)) (syn_cncs))) (Wff.classEq (Class.cv (nb076_alpha_dummy_005)) (Class.cab (nb076_alpha_dummy_000) (syn_wrex (nb076_alpha_dummy_001) (Class.cv (nb076_alpha_dummy_003)) (syn_wrex (nb076_alpha_dummy_002) (Class.cv (nb076_alpha_dummy_004)) (syn_wbr (Class.cv (nb076_alpha_dummy_000)) (syn_cen) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))))))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0001 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : m ∈ (({m} : Finset Var) ∪ ({n} : Finset Var) ∪ ({(nb076_alpha_dummy_006 g m n a b)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv m) (syn_cncs)) (Wff.classMem (Class.cv n) (syn_cncs))) (Wff.classEq (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Class.cab a (syn_wrex b (Class.cv m) (syn_wrex g (Class.cv n) (syn_wbr (Class.cv a) (syn_cen) (syn_cxp (Class.cv b) (Class.cv g))))))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0002 : (nb076_alpha_dummy_004) ∈ (({(nb076_alpha_dummy_003)} : Finset Var) ∪ ({(nb076_alpha_dummy_004)} : Finset Var) ∪ ({(nb076_alpha_dummy_005)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_003)) (syn_cncs)) (Wff.classMem (Class.cv (nb076_alpha_dummy_004)) (syn_cncs))) (Wff.classEq (Class.cv (nb076_alpha_dummy_005)) (Class.cab (nb076_alpha_dummy_000) (syn_wrex (nb076_alpha_dummy_001) (Class.cv (nb076_alpha_dummy_003)) (syn_wrex (nb076_alpha_dummy_002) (Class.cv (nb076_alpha_dummy_004)) (syn_wbr (Class.cv (nb076_alpha_dummy_000)) (syn_cen) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))))))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0003 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : n ∈ (({m} : Finset Var) ∪ ({n} : Finset Var) ∪ ({(nb076_alpha_dummy_006 g m n a b)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv m) (syn_cncs)) (Wff.classMem (Class.cv n) (syn_cncs))) (Wff.classEq (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Class.cab a (syn_wrex b (Class.cv m) (syn_wrex g (Class.cv n) (syn_wbr (Class.cv a) (syn_cen) (syn_cxp (Class.cv b) (Class.cv g))))))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0004 : (nb076_alpha_dummy_005) ∈ (({(nb076_alpha_dummy_003)} : Finset Var) ∪ ({(nb076_alpha_dummy_004)} : Finset Var) ∪ ({(nb076_alpha_dummy_005)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_003)) (syn_cncs)) (Wff.classMem (Class.cv (nb076_alpha_dummy_004)) (syn_cncs))) (Wff.classEq (Class.cv (nb076_alpha_dummy_005)) (Class.cab (nb076_alpha_dummy_000) (syn_wrex (nb076_alpha_dummy_001) (Class.cv (nb076_alpha_dummy_003)) (syn_wrex (nb076_alpha_dummy_002) (Class.cv (nb076_alpha_dummy_004)) (syn_wbr (Class.cv (nb076_alpha_dummy_000)) (syn_cen) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))))))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0005 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_006 g m n a b) ∈ (({m} : Finset Var) ∪ ({n} : Finset Var) ∪ ({(nb076_alpha_dummy_006 g m n a b)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv m) (syn_cncs)) (Wff.classMem (Class.cv n) (syn_cncs))) (Wff.classEq (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Class.cab a (syn_wrex b (Class.cv m) (syn_wrex g (Class.cv n) (syn_wbr (Class.cv a) (syn_cen) (syn_cxp (Class.cv b) (Class.cv g))))))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0006 : (nb076_alpha_dummy_003) ∈ (({(nb076_alpha_dummy_003)} : Finset Var) ∪ ((syn_cncs)).fv ∪ ({(nb076_alpha_dummy_004)} : Finset Var) ∪ ((syn_cncs)).fv ∪ ((Class.cab (nb076_alpha_dummy_000) (syn_wrex (nb076_alpha_dummy_001) (Class.cv (nb076_alpha_dummy_003)) (syn_wrex (nb076_alpha_dummy_002) (Class.cv (nb076_alpha_dummy_004)) (syn_wbr (Class.cv (nb076_alpha_dummy_000)) (syn_cen) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0007 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : m ∈ (({m} : Finset Var) ∪ ((syn_cncs)).fv ∪ ({n} : Finset Var) ∪ ((syn_cncs)).fv ∪ ((Class.cab a (syn_wrex b (Class.cv m) (syn_wrex g (Class.cv n) (syn_wbr (Class.cv a) (syn_cen) (syn_cxp (Class.cv b) (Class.cv g))))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0008 : (nb076_alpha_dummy_003) ∈ (((syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))).fv ∪ ((Class.cv (nb076_alpha_dummy_005))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cop]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0009 : (nb076_alpha_dummy_003) ∈ (((syn_ccompl (Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004))) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cphi (Class.cv (nb076_alpha_dummy_010)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005)) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0008) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0008) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0010 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : m ∈ (((syn_cop (Class.cv m) (Class.cv n))).fv ∪ ((Class.cv (nb076_alpha_dummy_006 g m n a b))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cop]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0011 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : m ∈ (((syn_ccompl (Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0010 g m n a b) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0010 g m n a b) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0012 : (nb076_alpha_dummy_003) ∈ (((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004))) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cphi (Class.cv (nb076_alpha_dummy_010))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004))) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cphi (Class.cv (nb076_alpha_dummy_010))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0008) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0008) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0013 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : m ∈ (((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0010 g m n a b) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0010 g m n a b) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0014 : (nb076_alpha_dummy_003) ∈ (((Class.cv (nb076_alpha_dummy_003))).fv ∪ ((Class.cv (nb076_alpha_dummy_004))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0015 : (nb076_alpha_dummy_003) ∈ (((syn_ccompl (Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cphi (Class.cv (nb076_alpha_dummy_018)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0014) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0014) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0016 (m : Var) (n : Var) : m ∈ (((Class.cv m)).fv ∪ ((Class.cv n)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0017 (m : Var) (n : Var) : m ∈ (((syn_ccompl (Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0016 m n) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0016 m n) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0018 : (nb076_alpha_dummy_003) ∈ (((Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cphi (Class.cv (nb076_alpha_dummy_018))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cphi (Class.cv (nb076_alpha_dummy_018))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0014) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0014) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0019 (m : Var) (n : Var) : m ∈ (((Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0016 m n) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0016 m n) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0020 : (nb076_alpha_dummy_018) ∈ (((Class.cv (nb076_alpha_dummy_018))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0021 (m : Var) (n : Var) : (nb076_alpha_dummy_020 m n) ∈ (((Class.cv (nb076_alpha_dummy_020 m n))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0022 : (nb076_alpha_dummy_025) ∈ (((Wff.classMem (Class.cv (nb076_alpha_dummy_025)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_025)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_025))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0023 (m : Var) (n : Var) : (nb076_alpha_dummy_027 m n) ∈ (((Wff.classMem (Class.cv (nb076_alpha_dummy_027 m n)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_027 m n)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_027 m n))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0024 : (nb076_alpha_dummy_025) ∈ (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0025 (m : Var) (n : Var) : (nb076_alpha_dummy_027 m n) ∈ (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0026 : (nb076_alpha_dummy_032) ∈ (((syn_cnin (Class.cv (nb076_alpha_dummy_032)) (Class.cv (nb076_alpha_dummy_033)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_032)) (Class.cv (nb076_alpha_dummy_033)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0027 (m : Var) (n : Var) : (nb076_alpha_dummy_035 m n) ∈ (((syn_cnin (Class.cv (nb076_alpha_dummy_035 m n)) (Class.cv (nb076_alpha_dummy_036 m n)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_035 m n)) (Class.cv (nb076_alpha_dummy_036 m n)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0028 : (nb076_alpha_dummy_032) ∈ (((Class.cv (nb076_alpha_dummy_032))).fv ∪ ((Class.cv (nb076_alpha_dummy_033))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0029 (m : Var) (n : Var) : (nb076_alpha_dummy_035 m n) ∈ (((Class.cv (nb076_alpha_dummy_035 m n))).fv ∪ ((Class.cv (nb076_alpha_dummy_036 m n))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0030 : (nb076_alpha_dummy_033) ∈ (((syn_cnin (Class.cv (nb076_alpha_dummy_032)) (Class.cv (nb076_alpha_dummy_033)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_032)) (Class.cv (nb076_alpha_dummy_033)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0031 (m : Var) (n : Var) : (nb076_alpha_dummy_036 m n) ∈ (((syn_cnin (Class.cv (nb076_alpha_dummy_035 m n)) (Class.cv (nb076_alpha_dummy_036 m n)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_035 m n)) (Class.cv (nb076_alpha_dummy_036 m n)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0032 : (nb076_alpha_dummy_033) ∈ (((Class.cv (nb076_alpha_dummy_032))).fv ∪ ((Class.cv (nb076_alpha_dummy_033))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0033 (m : Var) (n : Var) : (nb076_alpha_dummy_036 m n) ∈ (((Class.cv (nb076_alpha_dummy_035 m n))).fv ∪ ((Class.cv (nb076_alpha_dummy_036 m n))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0034 : (nb076_alpha_dummy_032) ∈ (((syn_ccompl (Class.cv (nb076_alpha_dummy_032)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_033)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0035 (m : Var) (n : Var) : (nb076_alpha_dummy_035 m n) ∈ (((syn_ccompl (Class.cv (nb076_alpha_dummy_035 m n)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_036 m n)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0036 : (nb076_alpha_dummy_032) ∈ (((Class.cv (nb076_alpha_dummy_032))).fv ∪ ((Class.cv (nb076_alpha_dummy_032))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0037 (m : Var) (n : Var) : (nb076_alpha_dummy_035 m n) ∈ (((Class.cv (nb076_alpha_dummy_035 m n))).fv ∪ ((Class.cv (nb076_alpha_dummy_035 m n))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0038 : (nb076_alpha_dummy_033) ∈ (((syn_ccompl (Class.cv (nb076_alpha_dummy_032)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_033)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0039 (m : Var) (n : Var) : (nb076_alpha_dummy_036 m n) ∈ (((syn_ccompl (Class.cv (nb076_alpha_dummy_035 m n)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_036 m n)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0040 : (nb076_alpha_dummy_033) ∈ (((Class.cv (nb076_alpha_dummy_033))).fv ∪ ((Class.cv (nb076_alpha_dummy_033))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0041 (m : Var) (n : Var) : (nb076_alpha_dummy_036 m n) ∈ (((Class.cv (nb076_alpha_dummy_036 m n))).fv ∪ ((Class.cv (nb076_alpha_dummy_036 m n))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0042 : (nb076_alpha_dummy_004) ∈ (({(nb076_alpha_dummy_003)} : Finset Var) ∪ ((syn_cncs)).fv ∪ ({(nb076_alpha_dummy_004)} : Finset Var) ∪ ((syn_cncs)).fv ∪ ((Class.cab (nb076_alpha_dummy_000) (syn_wrex (nb076_alpha_dummy_001) (Class.cv (nb076_alpha_dummy_003)) (syn_wrex (nb076_alpha_dummy_002) (Class.cv (nb076_alpha_dummy_004)) (syn_wbr (Class.cv (nb076_alpha_dummy_000)) (syn_cen) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0043 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : n ∈ (({m} : Finset Var) ∪ ((syn_cncs)).fv ∪ ({n} : Finset Var) ∪ ((syn_cncs)).fv ∪ ((Class.cab a (syn_wrex b (Class.cv m) (syn_wrex g (Class.cv n) (syn_wbr (Class.cv a) (syn_cen) (syn_cxp (Class.cv b) (Class.cv g))))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0044 : (nb076_alpha_dummy_004) ∈ (((syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))).fv ∪ ((Class.cv (nb076_alpha_dummy_005))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cop]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0045 : (nb076_alpha_dummy_004) ∈ (((syn_ccompl (Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004))) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cphi (Class.cv (nb076_alpha_dummy_010)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005)) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0044) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0044) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0046 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : n ∈ (((syn_cop (Class.cv m) (Class.cv n))).fv ∪ ((Class.cv (nb076_alpha_dummy_006 g m n a b))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cop]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0047 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : n ∈ (((syn_ccompl (Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0046 g m n a b) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0046 g m n a b) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
