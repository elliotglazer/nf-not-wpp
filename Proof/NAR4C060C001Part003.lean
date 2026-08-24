import NAR4C060C001Part002

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

theorem nb060_fresh_149 (y : Var) (z : Var) : (nb060_alpha_dummy_084 y z) ∉ (((syn_ccompl (Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb060_alpha_dummy_084] using freshVar_not_mem (((syn_ccompl (Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb060_fresh_150 : (nb060_alpha_dummy_119) ∉ (((syn_ccompl (Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cphi (Class.cv (nb060_alpha_dummy_116)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb060_alpha_dummy_119] using freshVar_not_mem (((syn_ccompl (Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cphi (Class.cv (nb060_alpha_dummy_116)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb060_fresh_151 (x : Var) (z : Var) : (nb060_alpha_dummy_120 x z) ∉ (((syn_ccompl (Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb060_alpha_dummy_120] using freshVar_not_mem (((syn_ccompl (Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb060_fresh_152 : (nb060_alpha_dummy_031) ∉ (((syn_ccompl (Class.cv (nb060_alpha_dummy_022)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_023)))).fv) := by
  simpa only [nb060_alpha_dummy_031] using freshVar_not_mem (((syn_ccompl (Class.cv (nb060_alpha_dummy_022)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_023)))).fv) 0

theorem nb060_fresh_153 (r : Var) (a : Var) : (nb060_alpha_dummy_032 r a) ∉ (((syn_ccompl (Class.cv (nb060_alpha_dummy_025 r a)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_026 r a)))).fv) := by
  simpa only [nb060_alpha_dummy_032] using freshVar_not_mem (((syn_ccompl (Class.cv (nb060_alpha_dummy_025 r a)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_026 r a)))).fv) 0

theorem nb060_fresh_154 : (nb060_alpha_dummy_067) ∉ (((syn_ccompl (Class.cv (nb060_alpha_dummy_058)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_059)))).fv) := by
  simpa only [nb060_alpha_dummy_067] using freshVar_not_mem (((syn_ccompl (Class.cv (nb060_alpha_dummy_058)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_059)))).fv) 0

theorem nb060_fresh_155 (x : Var) (y : Var) : (nb060_alpha_dummy_068 x y) ∉ (((syn_ccompl (Class.cv (nb060_alpha_dummy_061 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_062 x y)))).fv) := by
  simpa only [nb060_alpha_dummy_068] using freshVar_not_mem (((syn_ccompl (Class.cv (nb060_alpha_dummy_061 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_062 x y)))).fv) 0

theorem nb060_fresh_156 : (nb060_alpha_dummy_103) ∉ (((syn_ccompl (Class.cv (nb060_alpha_dummy_094)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_095)))).fv) := by
  simpa only [nb060_alpha_dummy_103] using freshVar_not_mem (((syn_ccompl (Class.cv (nb060_alpha_dummy_094)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_095)))).fv) 0

theorem nb060_fresh_157 (y : Var) (z : Var) : (nb060_alpha_dummy_104 y z) ∉ (((syn_ccompl (Class.cv (nb060_alpha_dummy_097 y z)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_098 y z)))).fv) := by
  simpa only [nb060_alpha_dummy_104] using freshVar_not_mem (((syn_ccompl (Class.cv (nb060_alpha_dummy_097 y z)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_098 y z)))).fv) 0

theorem nb060_fresh_158 : (nb060_alpha_dummy_139) ∉ (((syn_ccompl (Class.cv (nb060_alpha_dummy_130)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_131)))).fv) := by
  simpa only [nb060_alpha_dummy_139] using freshVar_not_mem (((syn_ccompl (Class.cv (nb060_alpha_dummy_130)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_131)))).fv) 0

theorem nb060_fresh_159 (x : Var) (z : Var) : (nb060_alpha_dummy_140 x z) ∉ (((syn_ccompl (Class.cv (nb060_alpha_dummy_133 x z)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_134 x z)))).fv) := by
  simpa only [nb060_alpha_dummy_140] using freshVar_not_mem (((syn_ccompl (Class.cv (nb060_alpha_dummy_133 x z)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_134 x z)))).fv) 0

theorem nb060_fresh_160 : (nb060_alpha_dummy_039) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_008))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb060_alpha_dummy_039] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_008))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb060_fresh_161 (r : Var) (a : Var) : (nb060_alpha_dummy_040 r a) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb060_alpha_dummy_040] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb060_fresh_162 : (nb060_alpha_dummy_075) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_044))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb060_alpha_dummy_075] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_044))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb060_fresh_163 (x : Var) (y : Var) : (nb060_alpha_dummy_076 x y) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb060_alpha_dummy_076] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb060_fresh_164 : (nb060_alpha_dummy_111) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_080))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb060_alpha_dummy_111] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_080))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb060_fresh_165 (y : Var) (z : Var) : (nb060_alpha_dummy_112 y z) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb060_alpha_dummy_112] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb060_fresh_166 : (nb060_alpha_dummy_147) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_116))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb060_alpha_dummy_147] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_116))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb060_fresh_167 (x : Var) (z : Var) : (nb060_alpha_dummy_148 x z) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb060_alpha_dummy_148] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb060_fresh_168 : (nb060_alpha_dummy_027) ∉ (((syn_cnin (Class.cv (nb060_alpha_dummy_022)) (Class.cv (nb060_alpha_dummy_023)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_022)) (Class.cv (nb060_alpha_dummy_023)))).fv) := by
  simpa only [nb060_alpha_dummy_027] using freshVar_not_mem (((syn_cnin (Class.cv (nb060_alpha_dummy_022)) (Class.cv (nb060_alpha_dummy_023)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_022)) (Class.cv (nb060_alpha_dummy_023)))).fv) 0

theorem nb060_fresh_169 (r : Var) (a : Var) : (nb060_alpha_dummy_028 r a) ∉ (((syn_cnin (Class.cv (nb060_alpha_dummy_025 r a)) (Class.cv (nb060_alpha_dummy_026 r a)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_025 r a)) (Class.cv (nb060_alpha_dummy_026 r a)))).fv) := by
  simpa only [nb060_alpha_dummy_028] using freshVar_not_mem (((syn_cnin (Class.cv (nb060_alpha_dummy_025 r a)) (Class.cv (nb060_alpha_dummy_026 r a)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_025 r a)) (Class.cv (nb060_alpha_dummy_026 r a)))).fv) 0

theorem nb060_fresh_170 : (nb060_alpha_dummy_063) ∉ (((syn_cnin (Class.cv (nb060_alpha_dummy_058)) (Class.cv (nb060_alpha_dummy_059)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_058)) (Class.cv (nb060_alpha_dummy_059)))).fv) := by
  simpa only [nb060_alpha_dummy_063] using freshVar_not_mem (((syn_cnin (Class.cv (nb060_alpha_dummy_058)) (Class.cv (nb060_alpha_dummy_059)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_058)) (Class.cv (nb060_alpha_dummy_059)))).fv) 0

theorem nb060_fresh_171 (x : Var) (y : Var) : (nb060_alpha_dummy_064 x y) ∉ (((syn_cnin (Class.cv (nb060_alpha_dummy_061 x y)) (Class.cv (nb060_alpha_dummy_062 x y)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_061 x y)) (Class.cv (nb060_alpha_dummy_062 x y)))).fv) := by
  simpa only [nb060_alpha_dummy_064] using freshVar_not_mem (((syn_cnin (Class.cv (nb060_alpha_dummy_061 x y)) (Class.cv (nb060_alpha_dummy_062 x y)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_061 x y)) (Class.cv (nb060_alpha_dummy_062 x y)))).fv) 0

theorem nb060_fresh_172 : (nb060_alpha_dummy_099) ∉ (((syn_cnin (Class.cv (nb060_alpha_dummy_094)) (Class.cv (nb060_alpha_dummy_095)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_094)) (Class.cv (nb060_alpha_dummy_095)))).fv) := by
  simpa only [nb060_alpha_dummy_099] using freshVar_not_mem (((syn_cnin (Class.cv (nb060_alpha_dummy_094)) (Class.cv (nb060_alpha_dummy_095)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_094)) (Class.cv (nb060_alpha_dummy_095)))).fv) 0

theorem nb060_fresh_173 (y : Var) (z : Var) : (nb060_alpha_dummy_100 y z) ∉ (((syn_cnin (Class.cv (nb060_alpha_dummy_097 y z)) (Class.cv (nb060_alpha_dummy_098 y z)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_097 y z)) (Class.cv (nb060_alpha_dummy_098 y z)))).fv) := by
  simpa only [nb060_alpha_dummy_100] using freshVar_not_mem (((syn_cnin (Class.cv (nb060_alpha_dummy_097 y z)) (Class.cv (nb060_alpha_dummy_098 y z)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_097 y z)) (Class.cv (nb060_alpha_dummy_098 y z)))).fv) 0

theorem nb060_fresh_174 : (nb060_alpha_dummy_135) ∉ (((syn_cnin (Class.cv (nb060_alpha_dummy_130)) (Class.cv (nb060_alpha_dummy_131)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_130)) (Class.cv (nb060_alpha_dummy_131)))).fv) := by
  simpa only [nb060_alpha_dummy_135] using freshVar_not_mem (((syn_cnin (Class.cv (nb060_alpha_dummy_130)) (Class.cv (nb060_alpha_dummy_131)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_130)) (Class.cv (nb060_alpha_dummy_131)))).fv) 0

theorem nb060_fresh_175 (x : Var) (z : Var) : (nb060_alpha_dummy_136 x z) ∉ (((syn_cnin (Class.cv (nb060_alpha_dummy_133 x z)) (Class.cv (nb060_alpha_dummy_134 x z)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_133 x z)) (Class.cv (nb060_alpha_dummy_134 x z)))).fv) := by
  simpa only [nb060_alpha_dummy_136] using freshVar_not_mem (((syn_cnin (Class.cv (nb060_alpha_dummy_133 x z)) (Class.cv (nb060_alpha_dummy_134 x z)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_133 x z)) (Class.cv (nb060_alpha_dummy_134 x z)))).fv) 0

theorem nb060_fresh_176 : (nb060_alpha_dummy_041) ∉ (((syn_cphi (Class.cv (nb060_alpha_dummy_008)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_008)))).fv) := by
  simpa only [nb060_alpha_dummy_041] using freshVar_not_mem (((syn_cphi (Class.cv (nb060_alpha_dummy_008)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_008)))).fv) 0

theorem nb060_fresh_177 (r : Var) (a : Var) : (nb060_alpha_dummy_042 r a) ∉ (((syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))).fv) := by
  simpa only [nb060_alpha_dummy_042] using freshVar_not_mem (((syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))).fv) 0

theorem nb060_fresh_178 : (nb060_alpha_dummy_077) ∉ (((syn_cphi (Class.cv (nb060_alpha_dummy_044)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_044)))).fv) := by
  simpa only [nb060_alpha_dummy_077] using freshVar_not_mem (((syn_cphi (Class.cv (nb060_alpha_dummy_044)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_044)))).fv) 0

theorem nb060_fresh_179 (x : Var) (y : Var) : (nb060_alpha_dummy_078 x y) ∉ (((syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))).fv) := by
  simpa only [nb060_alpha_dummy_078] using freshVar_not_mem (((syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))).fv) 0

theorem nb060_fresh_180 : (nb060_alpha_dummy_113) ∉ (((syn_cphi (Class.cv (nb060_alpha_dummy_080)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_080)))).fv) := by
  simpa only [nb060_alpha_dummy_113] using freshVar_not_mem (((syn_cphi (Class.cv (nb060_alpha_dummy_080)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_080)))).fv) 0

theorem nb060_fresh_181 (y : Var) (z : Var) : (nb060_alpha_dummy_114 y z) ∉ (((syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))).fv) := by
  simpa only [nb060_alpha_dummy_114] using freshVar_not_mem (((syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))).fv) 0

theorem nb060_fresh_182 : (nb060_alpha_dummy_149) ∉ (((syn_cphi (Class.cv (nb060_alpha_dummy_116)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_116)))).fv) := by
  simpa only [nb060_alpha_dummy_149] using freshVar_not_mem (((syn_cphi (Class.cv (nb060_alpha_dummy_116)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_116)))).fv) 0

theorem nb060_fresh_183 (x : Var) (z : Var) : (nb060_alpha_dummy_150 x z) ∉ (((syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))).fv) := by
  simpa only [nb060_alpha_dummy_150] using freshVar_not_mem (((syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))).fv) 0

theorem nb060_fresh_184 : (nb060_alpha_dummy_005) ∉ (({(nb060_alpha_dummy_001)} : Finset Var) ∪ ({(nb060_alpha_dummy_000)} : Finset Var) ∪ ((syn_wral (nb060_alpha_dummy_002) (Class.cv (nb060_alpha_dummy_000)) (syn_wral (nb060_alpha_dummy_003) (Class.cv (nb060_alpha_dummy_000)) (syn_wral (nb060_alpha_dummy_004) (Class.cv (nb060_alpha_dummy_000)) (Wff.imp (syn_wa (syn_wbr (Class.cv (nb060_alpha_dummy_002)) (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_003))) (syn_wbr (Class.cv (nb060_alpha_dummy_003)) (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_004)))) (syn_wbr (Class.cv (nb060_alpha_dummy_002)) (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_004)))))))).fv) := by
  simpa only [nb060_alpha_dummy_005] using freshVar_not_mem (({(nb060_alpha_dummy_001)} : Finset Var) ∪ ({(nb060_alpha_dummy_000)} : Finset Var) ∪ ((syn_wral (nb060_alpha_dummy_002) (Class.cv (nb060_alpha_dummy_000)) (syn_wral (nb060_alpha_dummy_003) (Class.cv (nb060_alpha_dummy_000)) (syn_wral (nb060_alpha_dummy_004) (Class.cv (nb060_alpha_dummy_000)) (Wff.imp (syn_wa (syn_wbr (Class.cv (nb060_alpha_dummy_002)) (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_003))) (syn_wbr (Class.cv (nb060_alpha_dummy_003)) (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_004)))) (syn_wbr (Class.cv (nb060_alpha_dummy_002)) (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_004)))))))).fv) 0

theorem nb060_fresh_185 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : (nb060_alpha_dummy_006 x y z r a) ∉ (({r} : Finset Var) ∪ ({a} : Finset Var) ∪ ((syn_wral x (Class.cv a) (syn_wral y (Class.cv a) (syn_wral z (Class.cv a) (Wff.imp (syn_wa (syn_wbr (Class.cv x) (Class.cv r) (Class.cv y)) (syn_wbr (Class.cv y) (Class.cv r) (Class.cv z))) (syn_wbr (Class.cv x) (Class.cv r) (Class.cv z))))))).fv) := by
  simpa only [nb060_alpha_dummy_006] using freshVar_not_mem (({r} : Finset Var) ∪ ({a} : Finset Var) ∪ ((syn_wral x (Class.cv a) (syn_wral y (Class.cv a) (syn_wral z (Class.cv a) (Wff.imp (syn_wa (syn_wbr (Class.cv x) (Class.cv r) (Class.cv y)) (syn_wbr (Class.cv y) (Class.cv r) (Class.cv z))) (syn_wbr (Class.cv x) (Class.cv r) (Class.cv z))))))).fv) 0

theorem nb060_fresh_186 : (nb060_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb060_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb060_fresh_187 : (nb060_alpha_dummy_001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb060_alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb060_fresh_188 : (nb060_alpha_dummy_002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb060_alpha_dummy_002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb060_fresh_189 : (nb060_alpha_dummy_003) ∉ ((∅ : Finset Var)) := by
  simpa only [nb060_alpha_dummy_003] using freshVar_not_mem ((∅ : Finset Var)) 3

theorem nb060_fresh_190 : (nb060_alpha_dummy_004) ∉ ((∅ : Finset Var)) := by
  simpa only [nb060_alpha_dummy_004] using freshVar_not_mem ((∅ : Finset Var)) 4

theorem nb060_distinct_191 : (nb060_alpha_dummy_000) ≠ (nb060_alpha_dummy_001) := by
  simpa only [nb060_alpha_dummy_000, nb060_alpha_dummy_001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb060_distinct_192 : (nb060_alpha_dummy_000) ≠ (nb060_alpha_dummy_002) := by
  simpa only [nb060_alpha_dummy_000, nb060_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb060_distinct_193 : (nb060_alpha_dummy_000) ≠ (nb060_alpha_dummy_003) := by
  simpa only [nb060_alpha_dummy_000, nb060_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 3) (by decide))

theorem nb060_distinct_194 : (nb060_alpha_dummy_000) ≠ (nb060_alpha_dummy_004) := by
  simpa only [nb060_alpha_dummy_000, nb060_alpha_dummy_004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 4) (by decide))

theorem nb060_distinct_195 : (nb060_alpha_dummy_001) ≠ (nb060_alpha_dummy_002) := by
  simpa only [nb060_alpha_dummy_001, nb060_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb060_distinct_196 : (nb060_alpha_dummy_001) ≠ (nb060_alpha_dummy_003) := by
  simpa only [nb060_alpha_dummy_001, nb060_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 3) (by decide))

theorem nb060_distinct_197 : (nb060_alpha_dummy_001) ≠ (nb060_alpha_dummy_004) := by
  simpa only [nb060_alpha_dummy_001, nb060_alpha_dummy_004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 4) (by decide))

theorem nb060_distinct_198 : (nb060_alpha_dummy_002) ≠ (nb060_alpha_dummy_003) := by
  simpa only [nb060_alpha_dummy_002, nb060_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 3) (by decide))

theorem nb060_distinct_199 : (nb060_alpha_dummy_002) ≠ (nb060_alpha_dummy_004) := by
  simpa only [nb060_alpha_dummy_002, nb060_alpha_dummy_004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 4) (by decide))

theorem nb060_distinct_200 : (nb060_alpha_dummy_003) ≠ (nb060_alpha_dummy_004) := by
  simpa only [nb060_alpha_dummy_003, nb060_alpha_dummy_004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 3) (j := 4) (by decide))

theorem nb060_support_mem_0000 : (nb060_alpha_dummy_001) ∈ (({(nb060_alpha_dummy_001)} : Finset Var) ∪ ({(nb060_alpha_dummy_000)} : Finset Var) ∪ ((syn_wral (nb060_alpha_dummy_002) (Class.cv (nb060_alpha_dummy_000)) (syn_wral (nb060_alpha_dummy_003) (Class.cv (nb060_alpha_dummy_000)) (syn_wral (nb060_alpha_dummy_004) (Class.cv (nb060_alpha_dummy_000)) (Wff.imp (syn_wa (syn_wbr (Class.cv (nb060_alpha_dummy_002)) (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_003))) (syn_wbr (Class.cv (nb060_alpha_dummy_003)) (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_004)))) (syn_wbr (Class.cv (nb060_alpha_dummy_002)) (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_004)))))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0001 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : r ∈ (({r} : Finset Var) ∪ ({a} : Finset Var) ∪ ((syn_wral x (Class.cv a) (syn_wral y (Class.cv a) (syn_wral z (Class.cv a) (Wff.imp (syn_wa (syn_wbr (Class.cv x) (Class.cv r) (Class.cv y)) (syn_wbr (Class.cv y) (Class.cv r) (Class.cv z))) (syn_wbr (Class.cv x) (Class.cv r) (Class.cv z))))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0002 : (nb060_alpha_dummy_000) ∈ (({(nb060_alpha_dummy_001)} : Finset Var) ∪ ({(nb060_alpha_dummy_000)} : Finset Var) ∪ ((syn_wral (nb060_alpha_dummy_002) (Class.cv (nb060_alpha_dummy_000)) (syn_wral (nb060_alpha_dummy_003) (Class.cv (nb060_alpha_dummy_000)) (syn_wral (nb060_alpha_dummy_004) (Class.cv (nb060_alpha_dummy_000)) (Wff.imp (syn_wa (syn_wbr (Class.cv (nb060_alpha_dummy_002)) (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_003))) (syn_wbr (Class.cv (nb060_alpha_dummy_003)) (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_004)))) (syn_wbr (Class.cv (nb060_alpha_dummy_002)) (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_004)))))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0003 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : a ∈ (({r} : Finset Var) ∪ ({a} : Finset Var) ∪ ((syn_wral x (Class.cv a) (syn_wral y (Class.cv a) (syn_wral z (Class.cv a) (Wff.imp (syn_wa (syn_wbr (Class.cv x) (Class.cv r) (Class.cv y)) (syn_wbr (Class.cv y) (Class.cv r) (Class.cv z))) (syn_wbr (Class.cv x) (Class.cv r) (Class.cv z))))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0004 : (nb060_alpha_dummy_001) ∈ (((Class.cv (nb060_alpha_dummy_001))).fv ∪ ((Class.cv (nb060_alpha_dummy_000))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0005 : (nb060_alpha_dummy_001) ∈ (((syn_ccompl (Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cphi (Class.cv (nb060_alpha_dummy_008)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0004) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0004) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0006 (r : Var) (a : Var) : r ∈ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0007 (r : Var) (a : Var) : r ∈ (((syn_ccompl (Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0006 r a) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0006 r a) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0008 : (nb060_alpha_dummy_001) ∈ (((Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cphi (Class.cv (nb060_alpha_dummy_008))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cphi (Class.cv (nb060_alpha_dummy_008))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0004) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0004) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0009 (r : Var) (a : Var) : r ∈ (((Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0006 r a) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0006 r a) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0010 : (nb060_alpha_dummy_008) ∈ (((Class.cv (nb060_alpha_dummy_008))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0011 (r : Var) (a : Var) : (nb060_alpha_dummy_010 r a) ∈ (((Class.cv (nb060_alpha_dummy_010 r a))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0012 : (nb060_alpha_dummy_015) ∈ (((Wff.classMem (Class.cv (nb060_alpha_dummy_015)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_015)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_015))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0013 (r : Var) (a : Var) : (nb060_alpha_dummy_017 r a) ∈ (((Wff.classMem (Class.cv (nb060_alpha_dummy_017 r a)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_017 r a)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_017 r a))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0014 : (nb060_alpha_dummy_015) ∈ (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0015 (r : Var) (a : Var) : (nb060_alpha_dummy_017 r a) ∈ (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0016 : (nb060_alpha_dummy_022) ∈ (((syn_cnin (Class.cv (nb060_alpha_dummy_022)) (Class.cv (nb060_alpha_dummy_023)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_022)) (Class.cv (nb060_alpha_dummy_023)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0017 (r : Var) (a : Var) : (nb060_alpha_dummy_025 r a) ∈ (((syn_cnin (Class.cv (nb060_alpha_dummy_025 r a)) (Class.cv (nb060_alpha_dummy_026 r a)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_025 r a)) (Class.cv (nb060_alpha_dummy_026 r a)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0018 : (nb060_alpha_dummy_022) ∈ (((Class.cv (nb060_alpha_dummy_022))).fv ∪ ((Class.cv (nb060_alpha_dummy_023))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0019 (r : Var) (a : Var) : (nb060_alpha_dummy_025 r a) ∈ (((Class.cv (nb060_alpha_dummy_025 r a))).fv ∪ ((Class.cv (nb060_alpha_dummy_026 r a))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0020 : (nb060_alpha_dummy_023) ∈ (((syn_cnin (Class.cv (nb060_alpha_dummy_022)) (Class.cv (nb060_alpha_dummy_023)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_022)) (Class.cv (nb060_alpha_dummy_023)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0021 (r : Var) (a : Var) : (nb060_alpha_dummy_026 r a) ∈ (((syn_cnin (Class.cv (nb060_alpha_dummy_025 r a)) (Class.cv (nb060_alpha_dummy_026 r a)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_025 r a)) (Class.cv (nb060_alpha_dummy_026 r a)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0022 : (nb060_alpha_dummy_023) ∈ (((Class.cv (nb060_alpha_dummy_022))).fv ∪ ((Class.cv (nb060_alpha_dummy_023))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0023 (r : Var) (a : Var) : (nb060_alpha_dummy_026 r a) ∈ (((Class.cv (nb060_alpha_dummy_025 r a))).fv ∪ ((Class.cv (nb060_alpha_dummy_026 r a))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0024 : (nb060_alpha_dummy_022) ∈ (((syn_ccompl (Class.cv (nb060_alpha_dummy_022)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_023)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0025 (r : Var) (a : Var) : (nb060_alpha_dummy_025 r a) ∈ (((syn_ccompl (Class.cv (nb060_alpha_dummy_025 r a)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_026 r a)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0026 : (nb060_alpha_dummy_022) ∈ (((Class.cv (nb060_alpha_dummy_022))).fv ∪ ((Class.cv (nb060_alpha_dummy_022))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0027 (r : Var) (a : Var) : (nb060_alpha_dummy_025 r a) ∈ (((Class.cv (nb060_alpha_dummy_025 r a))).fv ∪ ((Class.cv (nb060_alpha_dummy_025 r a))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0028 : (nb060_alpha_dummy_023) ∈ (((syn_ccompl (Class.cv (nb060_alpha_dummy_022)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_023)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0029 (r : Var) (a : Var) : (nb060_alpha_dummy_026 r a) ∈ (((syn_ccompl (Class.cv (nb060_alpha_dummy_025 r a)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_026 r a)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0030 : (nb060_alpha_dummy_023) ∈ (((Class.cv (nb060_alpha_dummy_023))).fv ∪ ((Class.cv (nb060_alpha_dummy_023))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0031 (r : Var) (a : Var) : (nb060_alpha_dummy_026 r a) ∈ (((Class.cv (nb060_alpha_dummy_026 r a))).fv ∪ ((Class.cv (nb060_alpha_dummy_026 r a))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0032 : (nb060_alpha_dummy_000) ∈ (((Class.cv (nb060_alpha_dummy_001))).fv ∪ ((Class.cv (nb060_alpha_dummy_000))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0033 : (nb060_alpha_dummy_000) ∈ (((syn_ccompl (Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cphi (Class.cv (nb060_alpha_dummy_008)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0032) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0032) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0034 (r : Var) (a : Var) : a ∈ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0035 (r : Var) (a : Var) : a ∈ (((syn_ccompl (Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0034 r a) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0034 r a) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0036 : (nb060_alpha_dummy_000) ∈ (((Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0032) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0032) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0037 (r : Var) (a : Var) : a ∈ (((Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0034 r a) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0034 r a) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0038 : (nb060_alpha_dummy_008) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_008))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0039 (r : Var) (a : Var) : (nb060_alpha_dummy_010 r a) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0040 : (nb060_alpha_dummy_008) ∈ (((syn_cphi (Class.cv (nb060_alpha_dummy_008)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_008)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0041 (r : Var) (a : Var) : (nb060_alpha_dummy_010 r a) ∈ (((syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0042 : (nb060_alpha_dummy_002) ∈ (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_003))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0043 : (nb060_alpha_dummy_002) ∈ (((syn_ccompl (Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cphi (Class.cv (nb060_alpha_dummy_044)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0042) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0042) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0044 (x : Var) (y : Var) : x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0045 (x : Var) (y : Var) : x ∈ (((syn_ccompl (Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0044 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0044 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0046 : (nb060_alpha_dummy_002) ∈ (((Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cphi (Class.cv (nb060_alpha_dummy_044))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cphi (Class.cv (nb060_alpha_dummy_044))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0042) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0042) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0047 (x : Var) (y : Var) : x ∈ (((Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0044 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0044 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0048 : (nb060_alpha_dummy_044) ∈ (((Class.cv (nb060_alpha_dummy_044))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0049 (x : Var) (y : Var) : (nb060_alpha_dummy_046 x y) ∈ (((Class.cv (nb060_alpha_dummy_046 x y))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0050 : (nb060_alpha_dummy_051) ∈ (((Wff.classMem (Class.cv (nb060_alpha_dummy_051)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_051)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_051))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0051 (x : Var) (y : Var) : (nb060_alpha_dummy_053 x y) ∈ (((Wff.classMem (Class.cv (nb060_alpha_dummy_053 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_053 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_053 x y))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0052 : (nb060_alpha_dummy_051) ∈ (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0053 (x : Var) (y : Var) : (nb060_alpha_dummy_053 x y) ∈ (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0054 : (nb060_alpha_dummy_058) ∈ (((syn_cnin (Class.cv (nb060_alpha_dummy_058)) (Class.cv (nb060_alpha_dummy_059)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_058)) (Class.cv (nb060_alpha_dummy_059)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0055 (x : Var) (y : Var) : (nb060_alpha_dummy_061 x y) ∈ (((syn_cnin (Class.cv (nb060_alpha_dummy_061 x y)) (Class.cv (nb060_alpha_dummy_062 x y)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_061 x y)) (Class.cv (nb060_alpha_dummy_062 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0056 : (nb060_alpha_dummy_058) ∈ (((Class.cv (nb060_alpha_dummy_058))).fv ∪ ((Class.cv (nb060_alpha_dummy_059))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0057 (x : Var) (y : Var) : (nb060_alpha_dummy_061 x y) ∈ (((Class.cv (nb060_alpha_dummy_061 x y))).fv ∪ ((Class.cv (nb060_alpha_dummy_062 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0058 : (nb060_alpha_dummy_059) ∈ (((syn_cnin (Class.cv (nb060_alpha_dummy_058)) (Class.cv (nb060_alpha_dummy_059)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_058)) (Class.cv (nb060_alpha_dummy_059)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0059 (x : Var) (y : Var) : (nb060_alpha_dummy_062 x y) ∈ (((syn_cnin (Class.cv (nb060_alpha_dummy_061 x y)) (Class.cv (nb060_alpha_dummy_062 x y)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_061 x y)) (Class.cv (nb060_alpha_dummy_062 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0060 : (nb060_alpha_dummy_059) ∈ (((Class.cv (nb060_alpha_dummy_058))).fv ∪ ((Class.cv (nb060_alpha_dummy_059))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0061 (x : Var) (y : Var) : (nb060_alpha_dummy_062 x y) ∈ (((Class.cv (nb060_alpha_dummy_061 x y))).fv ∪ ((Class.cv (nb060_alpha_dummy_062 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0062 : (nb060_alpha_dummy_058) ∈ (((syn_ccompl (Class.cv (nb060_alpha_dummy_058)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_059)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0063 (x : Var) (y : Var) : (nb060_alpha_dummy_061 x y) ∈ (((syn_ccompl (Class.cv (nb060_alpha_dummy_061 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_062 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0064 : (nb060_alpha_dummy_058) ∈ (((Class.cv (nb060_alpha_dummy_058))).fv ∪ ((Class.cv (nb060_alpha_dummy_058))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0065 (x : Var) (y : Var) : (nb060_alpha_dummy_061 x y) ∈ (((Class.cv (nb060_alpha_dummy_061 x y))).fv ∪ ((Class.cv (nb060_alpha_dummy_061 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0066 : (nb060_alpha_dummy_059) ∈ (((syn_ccompl (Class.cv (nb060_alpha_dummy_058)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_059)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0067 (x : Var) (y : Var) : (nb060_alpha_dummy_062 x y) ∈ (((syn_ccompl (Class.cv (nb060_alpha_dummy_061 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_062 x y)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0068 : (nb060_alpha_dummy_059) ∈ (((Class.cv (nb060_alpha_dummy_059))).fv ∪ ((Class.cv (nb060_alpha_dummy_059))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0069 (x : Var) (y : Var) : (nb060_alpha_dummy_062 x y) ∈ (((Class.cv (nb060_alpha_dummy_062 x y))).fv ∪ ((Class.cv (nb060_alpha_dummy_062 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0070 : (nb060_alpha_dummy_003) ∈ (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_003))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0071 : (nb060_alpha_dummy_003) ∈ (((syn_ccompl (Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cphi (Class.cv (nb060_alpha_dummy_044)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0070) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0070) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0072 (x : Var) (y : Var) : y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0073 (x : Var) (y : Var) : y ∈ (((syn_ccompl (Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0072 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0072 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0074 : (nb060_alpha_dummy_003) ∈ (((Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0070) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0070) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0075 (x : Var) (y : Var) : y ∈ (((Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0072 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0072 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0076 : (nb060_alpha_dummy_044) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_044))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0077 (x : Var) (y : Var) : (nb060_alpha_dummy_046 x y) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0078 : (nb060_alpha_dummy_044) ∈ (((syn_cphi (Class.cv (nb060_alpha_dummy_044)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_044)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0079 (x : Var) (y : Var) : (nb060_alpha_dummy_046 x y) ∈ (((syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0080 : (nb060_alpha_dummy_003) ∈ (((Class.cv (nb060_alpha_dummy_003))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0081 : (nb060_alpha_dummy_003) ∈ (((syn_ccompl (Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cphi (Class.cv (nb060_alpha_dummy_080)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0080) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0080) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0082 (y : Var) (z : Var) : y ∈ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0083 (y : Var) (z : Var) : y ∈ (((syn_ccompl (Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0082 y z) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0082 y z) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0084 : (nb060_alpha_dummy_003) ∈ (((Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cphi (Class.cv (nb060_alpha_dummy_080))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cphi (Class.cv (nb060_alpha_dummy_080))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0080) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0080) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
