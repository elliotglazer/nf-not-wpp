import NAR4C074C001Part001

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

noncomputable def nb074_alpha_dummy_150 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_141 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_141 x))).fv) 0)

noncomputable def nb074_alpha_dummy_151 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_139))).fv ∪ ((Class.cv (nb074_alpha_dummy_139))).fv) 0)

noncomputable def nb074_alpha_dummy_152 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_142 x))).fv) 0)

noncomputable def nb074_alpha_dummy_153 : Var := (freshVar (((Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb074_alpha_dummy_154 (x : Var) : Var := (freshVar (((Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb074_alpha_dummy_155 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_124))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb074_alpha_dummy_156 (x : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb074_alpha_dummy_157 : Var := (freshVar (((syn_cphi (Class.cv (nb074_alpha_dummy_124)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_124)))).fv) 0)

noncomputable def nb074_alpha_dummy_158 (x : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))).fv) 0)

theorem nb074_fresh_000 : (nb074_alpha_dummy_011) ∉ (((Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cphi (Class.cv (nb074_alpha_dummy_006))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cphi (Class.cv (nb074_alpha_dummy_006))))))).fv) := by
  simpa only [nb074_alpha_dummy_011] using freshVar_not_mem (((Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cphi (Class.cv (nb074_alpha_dummy_006))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cphi (Class.cv (nb074_alpha_dummy_006))))))).fv) 0

theorem nb074_fresh_001 : (nb074_alpha_dummy_035) ∉ (((Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb074_alpha_dummy_035] using freshVar_not_mem (((Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb074_fresh_002 (x : Var) : (nb074_alpha_dummy_036 x) ∉ (((Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb074_alpha_dummy_036] using freshVar_not_mem (((Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb074_fresh_003 (x : Var) : (nb074_alpha_dummy_012 x) ∉ (((Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))))))).fv) := by
  simpa only [nb074_alpha_dummy_012] using freshVar_not_mem (((Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))))))).fv) 0

theorem nb074_fresh_004 : (nb074_alpha_dummy_075) ∉ (((Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb074_alpha_dummy_075] using freshVar_not_mem (((Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb074_fresh_005 : (nb074_alpha_dummy_051) ∉ (((Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cphi (Class.cv (nb074_alpha_dummy_046))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cphi (Class.cv (nb074_alpha_dummy_046))))))).fv) := by
  simpa only [nb074_alpha_dummy_051] using freshVar_not_mem (((Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cphi (Class.cv (nb074_alpha_dummy_046))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cphi (Class.cv (nb074_alpha_dummy_046))))))).fv) 0

theorem nb074_fresh_006 (x : Var) : (nb074_alpha_dummy_076 x) ∉ (((Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb074_alpha_dummy_076] using freshVar_not_mem (((Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb074_fresh_007 (x : Var) : (nb074_alpha_dummy_052 x) ∉ (((Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))))))).fv) := by
  simpa only [nb074_alpha_dummy_052] using freshVar_not_mem (((Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))))))).fv) 0

theorem nb074_fresh_008 : (nb074_alpha_dummy_093) ∉ (((Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cphi (Class.cv (nb074_alpha_dummy_088))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cphi (Class.cv (nb074_alpha_dummy_088))))))).fv) := by
  simpa only [nb074_alpha_dummy_093] using freshVar_not_mem (((Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cphi (Class.cv (nb074_alpha_dummy_088))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cphi (Class.cv (nb074_alpha_dummy_088))))))).fv) 0

theorem nb074_fresh_009 : (nb074_alpha_dummy_117) ∉ (((Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb074_alpha_dummy_117] using freshVar_not_mem (((Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb074_fresh_010 (x : Var) : (nb074_alpha_dummy_094 x) ∉ (((Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))))).fv) := by
  simpa only [nb074_alpha_dummy_094] using freshVar_not_mem (((Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))))).fv) 0

theorem nb074_fresh_011 (x : Var) : (nb074_alpha_dummy_118 x) ∉ (((Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb074_alpha_dummy_118] using freshVar_not_mem (((Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb074_fresh_012 : (nb074_alpha_dummy_153) ∉ (((Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb074_alpha_dummy_153] using freshVar_not_mem (((Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb074_fresh_013 : (nb074_alpha_dummy_129) ∉ (((Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cphi (Class.cv (nb074_alpha_dummy_124))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cphi (Class.cv (nb074_alpha_dummy_124))))))).fv) := by
  simpa only [nb074_alpha_dummy_129] using freshVar_not_mem (((Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cphi (Class.cv (nb074_alpha_dummy_124))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cphi (Class.cv (nb074_alpha_dummy_124))))))).fv) 0

theorem nb074_fresh_014 (x : Var) : (nb074_alpha_dummy_154 x) ∉ (((Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb074_alpha_dummy_154] using freshVar_not_mem (((Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb074_fresh_015 (x : Var) : (nb074_alpha_dummy_130 x) ∉ (((Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))))).fv) := by
  simpa only [nb074_alpha_dummy_130] using freshVar_not_mem (((Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))))).fv) 0

theorem nb074_fresh_016 : (nb074_alpha_dummy_081) ∉ (((Class.cv (nb074_alpha_dummy_000))).fv) := by
  simpa only [nb074_alpha_dummy_081] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_000))).fv) 0

theorem nb074_fresh_017 : (nb074_alpha_dummy_082) ∉ (((Class.cv (nb074_alpha_dummy_000))).fv) := by
  simpa only [nb074_alpha_dummy_082] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_000))).fv) 1

theorem nb074_distinct_018 : (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_082) := by
  simpa only [nb074_alpha_dummy_081, nb074_alpha_dummy_082] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_000))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_019 : (nb074_alpha_dummy_005) ∉ (((Class.cv (nb074_alpha_dummy_000))).fv ∪ ((Class.cv (nb074_alpha_dummy_001))).fv) := by
  simpa only [nb074_alpha_dummy_005] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_000))).fv ∪ ((Class.cv (nb074_alpha_dummy_001))).fv) 0

theorem nb074_fresh_020 : (nb074_alpha_dummy_006) ∉ (((Class.cv (nb074_alpha_dummy_000))).fv ∪ ((Class.cv (nb074_alpha_dummy_001))).fv) := by
  simpa only [nb074_alpha_dummy_006] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_000))).fv ∪ ((Class.cv (nb074_alpha_dummy_001))).fv) 1

theorem nb074_distinct_021 : (nb074_alpha_dummy_005) ≠ (nb074_alpha_dummy_006) := by
  simpa only [nb074_alpha_dummy_005, nb074_alpha_dummy_006] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_000))).fv ∪ ((Class.cv (nb074_alpha_dummy_001))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_022 : (nb074_alpha_dummy_013) ∉ (((Class.cv (nb074_alpha_dummy_006))).fv) := by
  simpa only [nb074_alpha_dummy_013] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_006))).fv) 0

theorem nb074_fresh_023 : (nb074_alpha_dummy_014) ∉ (((Class.cv (nb074_alpha_dummy_006))).fv) := by
  simpa only [nb074_alpha_dummy_014] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_006))).fv) 1

theorem nb074_distinct_024 : (nb074_alpha_dummy_013) ≠ (nb074_alpha_dummy_014) := by
  simpa only [nb074_alpha_dummy_013, nb074_alpha_dummy_014] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_006))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_025 (x : Var) : (nb074_alpha_dummy_015 x) ∉ (((Class.cv (nb074_alpha_dummy_008 x))).fv) := by
  simpa only [nb074_alpha_dummy_015] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_008 x))).fv) 0

theorem nb074_fresh_026 (x : Var) : (nb074_alpha_dummy_016 x) ∉ (((Class.cv (nb074_alpha_dummy_008 x))).fv) := by
  simpa only [nb074_alpha_dummy_016] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_008 x))).fv) 1

theorem nb074_distinct_027 (x : Var) : (nb074_alpha_dummy_015 x) ≠ (nb074_alpha_dummy_016 x) := by
  simpa only [nb074_alpha_dummy_015, nb074_alpha_dummy_016] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_008 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_028 : (nb074_alpha_dummy_019) ∉ (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb074_alpha_dummy_019] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 0

theorem nb074_fresh_029 : (nb074_alpha_dummy_020) ∉ (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb074_alpha_dummy_020] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 1

theorem nb074_fresh_030 : (nb074_alpha_dummy_021) ∉ (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb074_alpha_dummy_021] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 2

theorem nb074_distinct_031 : (nb074_alpha_dummy_019) ≠ (nb074_alpha_dummy_020) := by
  simpa only [nb074_alpha_dummy_019, nb074_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb074_distinct_032 : (nb074_alpha_dummy_019) ≠ (nb074_alpha_dummy_021) := by
  simpa only [nb074_alpha_dummy_019, nb074_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb074_distinct_033 : (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_021) := by
  simpa only [nb074_alpha_dummy_020, nb074_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb074_fresh_034 (x : Var) : (nb074_alpha_dummy_022 x) ∉ (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb074_alpha_dummy_022] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb074_fresh_035 (x : Var) : (nb074_alpha_dummy_023 x) ∉ (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb074_alpha_dummy_023] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb074_fresh_036 (x : Var) : (nb074_alpha_dummy_024 x) ∉ (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb074_alpha_dummy_024] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb074_distinct_037 (x : Var) : (nb074_alpha_dummy_022 x) ≠ (nb074_alpha_dummy_023 x) := by
  simpa only [nb074_alpha_dummy_022, nb074_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb074_distinct_038 (x : Var) : (nb074_alpha_dummy_022 x) ≠ (nb074_alpha_dummy_024 x) := by
  simpa only [nb074_alpha_dummy_022, nb074_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb074_distinct_039 (x : Var) : (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_024 x) := by
  simpa only [nb074_alpha_dummy_023, nb074_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb074_fresh_040 : (nb074_alpha_dummy_031) ∉ (((Class.cv (nb074_alpha_dummy_020))).fv ∪ ((Class.cv (nb074_alpha_dummy_020))).fv) := by
  simpa only [nb074_alpha_dummy_031] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_020))).fv ∪ ((Class.cv (nb074_alpha_dummy_020))).fv) 0

theorem nb074_fresh_041 : (nb074_alpha_dummy_027) ∉ (((Class.cv (nb074_alpha_dummy_020))).fv ∪ ((Class.cv (nb074_alpha_dummy_021))).fv) := by
  simpa only [nb074_alpha_dummy_027] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_020))).fv ∪ ((Class.cv (nb074_alpha_dummy_021))).fv) 0

theorem nb074_fresh_042 : (nb074_alpha_dummy_033) ∉ (((Class.cv (nb074_alpha_dummy_021))).fv ∪ ((Class.cv (nb074_alpha_dummy_021))).fv) := by
  simpa only [nb074_alpha_dummy_033] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_021))).fv ∪ ((Class.cv (nb074_alpha_dummy_021))).fv) 0

theorem nb074_fresh_043 (x : Var) : (nb074_alpha_dummy_032 x) ∉ (((Class.cv (nb074_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_023 x))).fv) := by
  simpa only [nb074_alpha_dummy_032] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_023 x))).fv) 0

theorem nb074_fresh_044 (x : Var) : (nb074_alpha_dummy_028 x) ∉ (((Class.cv (nb074_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_024 x))).fv) := by
  simpa only [nb074_alpha_dummy_028] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_024 x))).fv) 0

theorem nb074_fresh_045 (x : Var) : (nb074_alpha_dummy_034 x) ∉ (((Class.cv (nb074_alpha_dummy_024 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_024 x))).fv) := by
  simpa only [nb074_alpha_dummy_034] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_024 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_024 x))).fv) 0

theorem nb074_fresh_046 : (nb074_alpha_dummy_045) ∉ (((Class.cv (nb074_alpha_dummy_042))).fv ∪ ((Class.cv (nb074_alpha_dummy_041))).fv) := by
  simpa only [nb074_alpha_dummy_045] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_042))).fv ∪ ((Class.cv (nb074_alpha_dummy_041))).fv) 0

theorem nb074_fresh_047 : (nb074_alpha_dummy_046) ∉ (((Class.cv (nb074_alpha_dummy_042))).fv ∪ ((Class.cv (nb074_alpha_dummy_041))).fv) := by
  simpa only [nb074_alpha_dummy_046] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_042))).fv ∪ ((Class.cv (nb074_alpha_dummy_041))).fv) 1

theorem nb074_distinct_048 : (nb074_alpha_dummy_045) ≠ (nb074_alpha_dummy_046) := by
  simpa only [nb074_alpha_dummy_045, nb074_alpha_dummy_046] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_042))).fv ∪ ((Class.cv (nb074_alpha_dummy_041))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_049 (x : Var) : (nb074_alpha_dummy_047 x) ∉ (((Class.cv (nb074_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_043 x))).fv) := by
  simpa only [nb074_alpha_dummy_047] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_043 x))).fv) 0

theorem nb074_fresh_050 (x : Var) : (nb074_alpha_dummy_048 x) ∉ (((Class.cv (nb074_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_043 x))).fv) := by
  simpa only [nb074_alpha_dummy_048] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_043 x))).fv) 1

theorem nb074_distinct_051 (x : Var) : (nb074_alpha_dummy_047 x) ≠ (nb074_alpha_dummy_048 x) := by
  simpa only [nb074_alpha_dummy_047, nb074_alpha_dummy_048] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_043 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_052 : (nb074_alpha_dummy_053) ∉ (((Class.cv (nb074_alpha_dummy_046))).fv) := by
  simpa only [nb074_alpha_dummy_053] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_046))).fv) 0

theorem nb074_fresh_053 : (nb074_alpha_dummy_054) ∉ (((Class.cv (nb074_alpha_dummy_046))).fv) := by
  simpa only [nb074_alpha_dummy_054] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_046))).fv) 1

theorem nb074_distinct_054 : (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_054) := by
  simpa only [nb074_alpha_dummy_053, nb074_alpha_dummy_054] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_046))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_055 (x : Var) : (nb074_alpha_dummy_055 x) ∉ (((Class.cv (nb074_alpha_dummy_048 x))).fv) := by
  simpa only [nb074_alpha_dummy_055] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_048 x))).fv) 0

theorem nb074_fresh_056 (x : Var) : (nb074_alpha_dummy_056 x) ∉ (((Class.cv (nb074_alpha_dummy_048 x))).fv) := by
  simpa only [nb074_alpha_dummy_056] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_048 x))).fv) 1

theorem nb074_distinct_057 (x : Var) : (nb074_alpha_dummy_055 x) ≠ (nb074_alpha_dummy_056 x) := by
  simpa only [nb074_alpha_dummy_055, nb074_alpha_dummy_056] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_048 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_058 : (nb074_alpha_dummy_059) ∉ (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb074_alpha_dummy_059] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 0

theorem nb074_fresh_059 : (nb074_alpha_dummy_060) ∉ (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb074_alpha_dummy_060] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 1

theorem nb074_fresh_060 : (nb074_alpha_dummy_061) ∉ (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb074_alpha_dummy_061] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 2

theorem nb074_distinct_061 : (nb074_alpha_dummy_059) ≠ (nb074_alpha_dummy_060) := by
  simpa only [nb074_alpha_dummy_059, nb074_alpha_dummy_060] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb074_distinct_062 : (nb074_alpha_dummy_059) ≠ (nb074_alpha_dummy_061) := by
  simpa only [nb074_alpha_dummy_059, nb074_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb074_distinct_063 : (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_061) := by
  simpa only [nb074_alpha_dummy_060, nb074_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb074_fresh_064 (x : Var) : (nb074_alpha_dummy_062 x) ∉ (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb074_alpha_dummy_062] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb074_fresh_065 (x : Var) : (nb074_alpha_dummy_063 x) ∉ (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb074_alpha_dummy_063] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb074_fresh_066 (x : Var) : (nb074_alpha_dummy_064 x) ∉ (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb074_alpha_dummy_064] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb074_distinct_067 (x : Var) : (nb074_alpha_dummy_062 x) ≠ (nb074_alpha_dummy_063 x) := by
  simpa only [nb074_alpha_dummy_062, nb074_alpha_dummy_063] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb074_distinct_068 (x : Var) : (nb074_alpha_dummy_062 x) ≠ (nb074_alpha_dummy_064 x) := by
  simpa only [nb074_alpha_dummy_062, nb074_alpha_dummy_064] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb074_distinct_069 (x : Var) : (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_064 x) := by
  simpa only [nb074_alpha_dummy_063, nb074_alpha_dummy_064] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb074_fresh_070 : (nb074_alpha_dummy_071) ∉ (((Class.cv (nb074_alpha_dummy_060))).fv ∪ ((Class.cv (nb074_alpha_dummy_060))).fv) := by
  simpa only [nb074_alpha_dummy_071] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_060))).fv ∪ ((Class.cv (nb074_alpha_dummy_060))).fv) 0

theorem nb074_fresh_071 : (nb074_alpha_dummy_067) ∉ (((Class.cv (nb074_alpha_dummy_060))).fv ∪ ((Class.cv (nb074_alpha_dummy_061))).fv) := by
  simpa only [nb074_alpha_dummy_067] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_060))).fv ∪ ((Class.cv (nb074_alpha_dummy_061))).fv) 0

theorem nb074_fresh_072 : (nb074_alpha_dummy_073) ∉ (((Class.cv (nb074_alpha_dummy_061))).fv ∪ ((Class.cv (nb074_alpha_dummy_061))).fv) := by
  simpa only [nb074_alpha_dummy_073] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_061))).fv ∪ ((Class.cv (nb074_alpha_dummy_061))).fv) 0

theorem nb074_fresh_073 (x : Var) : (nb074_alpha_dummy_072 x) ∉ (((Class.cv (nb074_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_063 x))).fv) := by
  simpa only [nb074_alpha_dummy_072] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_063 x))).fv) 0

theorem nb074_fresh_074 (x : Var) : (nb074_alpha_dummy_068 x) ∉ (((Class.cv (nb074_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_064 x))).fv) := by
  simpa only [nb074_alpha_dummy_068] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_064 x))).fv) 0

theorem nb074_fresh_075 (x : Var) : (nb074_alpha_dummy_074 x) ∉ (((Class.cv (nb074_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_064 x))).fv) := by
  simpa only [nb074_alpha_dummy_074] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_064 x))).fv) 0

theorem nb074_fresh_076 : (nb074_alpha_dummy_087) ∉ (((Class.cv (nb074_alpha_dummy_081))).fv ∪ ((Class.cv (nb074_alpha_dummy_082))).fv) := by
  simpa only [nb074_alpha_dummy_087] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_081))).fv ∪ ((Class.cv (nb074_alpha_dummy_082))).fv) 0

theorem nb074_fresh_077 : (nb074_alpha_dummy_088) ∉ (((Class.cv (nb074_alpha_dummy_081))).fv ∪ ((Class.cv (nb074_alpha_dummy_082))).fv) := by
  simpa only [nb074_alpha_dummy_088] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_081))).fv ∪ ((Class.cv (nb074_alpha_dummy_082))).fv) 1

theorem nb074_distinct_078 : (nb074_alpha_dummy_087) ≠ (nb074_alpha_dummy_088) := by
  simpa only [nb074_alpha_dummy_087, nb074_alpha_dummy_088] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_081))).fv ∪ ((Class.cv (nb074_alpha_dummy_082))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_079 : (nb074_alpha_dummy_123) ∉ (((Class.cv (nb074_alpha_dummy_082))).fv ∪ ((Class.cv (nb074_alpha_dummy_081))).fv) := by
  simpa only [nb074_alpha_dummy_123] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_082))).fv ∪ ((Class.cv (nb074_alpha_dummy_081))).fv) 0

theorem nb074_fresh_080 : (nb074_alpha_dummy_124) ∉ (((Class.cv (nb074_alpha_dummy_082))).fv ∪ ((Class.cv (nb074_alpha_dummy_081))).fv) := by
  simpa only [nb074_alpha_dummy_124] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_082))).fv ∪ ((Class.cv (nb074_alpha_dummy_081))).fv) 1

theorem nb074_distinct_081 : (nb074_alpha_dummy_123) ≠ (nb074_alpha_dummy_124) := by
  simpa only [nb074_alpha_dummy_123, nb074_alpha_dummy_124] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_082))).fv ∪ ((Class.cv (nb074_alpha_dummy_081))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_082 (x : Var) : (nb074_alpha_dummy_089 x) ∉ (((Class.cv (nb074_alpha_dummy_083 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_084 x))).fv) := by
  simpa only [nb074_alpha_dummy_089] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_083 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_084 x))).fv) 0

theorem nb074_fresh_083 (x : Var) : (nb074_alpha_dummy_090 x) ∉ (((Class.cv (nb074_alpha_dummy_083 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_084 x))).fv) := by
  simpa only [nb074_alpha_dummy_090] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_083 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_084 x))).fv) 1

theorem nb074_distinct_084 (x : Var) : (nb074_alpha_dummy_089 x) ≠ (nb074_alpha_dummy_090 x) := by
  simpa only [nb074_alpha_dummy_089, nb074_alpha_dummy_090] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_083 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_084 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_085 (x : Var) : (nb074_alpha_dummy_125 x) ∉ (((Class.cv (nb074_alpha_dummy_084 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_083 x))).fv) := by
  simpa only [nb074_alpha_dummy_125] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_084 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_083 x))).fv) 0

theorem nb074_fresh_086 (x : Var) : (nb074_alpha_dummy_126 x) ∉ (((Class.cv (nb074_alpha_dummy_084 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_083 x))).fv) := by
  simpa only [nb074_alpha_dummy_126] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_084 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_083 x))).fv) 1

theorem nb074_distinct_087 (x : Var) : (nb074_alpha_dummy_125 x) ≠ (nb074_alpha_dummy_126 x) := by
  simpa only [nb074_alpha_dummy_125, nb074_alpha_dummy_126] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_084 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_083 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_088 : (nb074_alpha_dummy_095) ∉ (((Class.cv (nb074_alpha_dummy_088))).fv) := by
  simpa only [nb074_alpha_dummy_095] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_088))).fv) 0

theorem nb074_fresh_089 : (nb074_alpha_dummy_096) ∉ (((Class.cv (nb074_alpha_dummy_088))).fv) := by
  simpa only [nb074_alpha_dummy_096] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_088))).fv) 1

theorem nb074_distinct_090 : (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_096) := by
  simpa only [nb074_alpha_dummy_095, nb074_alpha_dummy_096] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_088))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_091 (x : Var) : (nb074_alpha_dummy_097 x) ∉ (((Class.cv (nb074_alpha_dummy_090 x))).fv) := by
  simpa only [nb074_alpha_dummy_097] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_090 x))).fv) 0

theorem nb074_fresh_092 (x : Var) : (nb074_alpha_dummy_098 x) ∉ (((Class.cv (nb074_alpha_dummy_090 x))).fv) := by
  simpa only [nb074_alpha_dummy_098] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_090 x))).fv) 1

theorem nb074_distinct_093 (x : Var) : (nb074_alpha_dummy_097 x) ≠ (nb074_alpha_dummy_098 x) := by
  simpa only [nb074_alpha_dummy_097, nb074_alpha_dummy_098] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_090 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_094 : (nb074_alpha_dummy_101) ∉ (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb074_alpha_dummy_101] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) 0

theorem nb074_fresh_095 : (nb074_alpha_dummy_102) ∉ (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb074_alpha_dummy_102] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) 1

theorem nb074_fresh_096 : (nb074_alpha_dummy_103) ∉ (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb074_alpha_dummy_103] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) 2

theorem nb074_distinct_097 : (nb074_alpha_dummy_101) ≠ (nb074_alpha_dummy_102) := by
  simpa only [nb074_alpha_dummy_101, nb074_alpha_dummy_102] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb074_distinct_098 : (nb074_alpha_dummy_101) ≠ (nb074_alpha_dummy_103) := by
  simpa only [nb074_alpha_dummy_101, nb074_alpha_dummy_103] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb074_distinct_099 : (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_103) := by
  simpa only [nb074_alpha_dummy_102, nb074_alpha_dummy_103] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb074_fresh_100 (x : Var) : (nb074_alpha_dummy_104 x) ∉ (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb074_alpha_dummy_104] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb074_fresh_101 (x : Var) : (nb074_alpha_dummy_105 x) ∉ (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb074_alpha_dummy_105] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb074_fresh_102 (x : Var) : (nb074_alpha_dummy_106 x) ∉ (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb074_alpha_dummy_106] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb074_distinct_103 (x : Var) : (nb074_alpha_dummy_104 x) ≠ (nb074_alpha_dummy_105 x) := by
  simpa only [nb074_alpha_dummy_104, nb074_alpha_dummy_105] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb074_distinct_104 (x : Var) : (nb074_alpha_dummy_104 x) ≠ (nb074_alpha_dummy_106 x) := by
  simpa only [nb074_alpha_dummy_104, nb074_alpha_dummy_106] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb074_distinct_105 (x : Var) : (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_106 x) := by
  simpa only [nb074_alpha_dummy_105, nb074_alpha_dummy_106] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb074_fresh_106 : (nb074_alpha_dummy_113) ∉ (((Class.cv (nb074_alpha_dummy_102))).fv ∪ ((Class.cv (nb074_alpha_dummy_102))).fv) := by
  simpa only [nb074_alpha_dummy_113] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_102))).fv ∪ ((Class.cv (nb074_alpha_dummy_102))).fv) 0

theorem nb074_fresh_107 : (nb074_alpha_dummy_109) ∉ (((Class.cv (nb074_alpha_dummy_102))).fv ∪ ((Class.cv (nb074_alpha_dummy_103))).fv) := by
  simpa only [nb074_alpha_dummy_109] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_102))).fv ∪ ((Class.cv (nb074_alpha_dummy_103))).fv) 0

theorem nb074_fresh_108 : (nb074_alpha_dummy_115) ∉ (((Class.cv (nb074_alpha_dummy_103))).fv ∪ ((Class.cv (nb074_alpha_dummy_103))).fv) := by
  simpa only [nb074_alpha_dummy_115] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_103))).fv ∪ ((Class.cv (nb074_alpha_dummy_103))).fv) 0

theorem nb074_fresh_109 (x : Var) : (nb074_alpha_dummy_114 x) ∉ (((Class.cv (nb074_alpha_dummy_105 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_105 x))).fv) := by
  simpa only [nb074_alpha_dummy_114] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_105 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_105 x))).fv) 0

theorem nb074_fresh_110 (x : Var) : (nb074_alpha_dummy_110 x) ∉ (((Class.cv (nb074_alpha_dummy_105 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_106 x))).fv) := by
  simpa only [nb074_alpha_dummy_110] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_105 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_106 x))).fv) 0

theorem nb074_fresh_111 (x : Var) : (nb074_alpha_dummy_116 x) ∉ (((Class.cv (nb074_alpha_dummy_106 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_106 x))).fv) := by
  simpa only [nb074_alpha_dummy_116] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_106 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_106 x))).fv) 0

theorem nb074_fresh_112 : (nb074_alpha_dummy_131) ∉ (((Class.cv (nb074_alpha_dummy_124))).fv) := by
  simpa only [nb074_alpha_dummy_131] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_124))).fv) 0

theorem nb074_fresh_113 : (nb074_alpha_dummy_132) ∉ (((Class.cv (nb074_alpha_dummy_124))).fv) := by
  simpa only [nb074_alpha_dummy_132] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_124))).fv) 1

theorem nb074_distinct_114 : (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_132) := by
  simpa only [nb074_alpha_dummy_131, nb074_alpha_dummy_132] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_124))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_115 (x : Var) : (nb074_alpha_dummy_133 x) ∉ (((Class.cv (nb074_alpha_dummy_126 x))).fv) := by
  simpa only [nb074_alpha_dummy_133] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_126 x))).fv) 0

theorem nb074_fresh_116 (x : Var) : (nb074_alpha_dummy_134 x) ∉ (((Class.cv (nb074_alpha_dummy_126 x))).fv) := by
  simpa only [nb074_alpha_dummy_134] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_126 x))).fv) 1

theorem nb074_distinct_117 (x : Var) : (nb074_alpha_dummy_133 x) ≠ (nb074_alpha_dummy_134 x) := by
  simpa only [nb074_alpha_dummy_133, nb074_alpha_dummy_134] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_126 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_118 : (nb074_alpha_dummy_137) ∉ (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb074_alpha_dummy_137] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) 0

theorem nb074_fresh_119 : (nb074_alpha_dummy_138) ∉ (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb074_alpha_dummy_138] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) 1

theorem nb074_fresh_120 : (nb074_alpha_dummy_139) ∉ (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb074_alpha_dummy_139] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) 2

theorem nb074_distinct_121 : (nb074_alpha_dummy_137) ≠ (nb074_alpha_dummy_138) := by
  simpa only [nb074_alpha_dummy_137, nb074_alpha_dummy_138] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb074_distinct_122 : (nb074_alpha_dummy_137) ≠ (nb074_alpha_dummy_139) := by
  simpa only [nb074_alpha_dummy_137, nb074_alpha_dummy_139] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb074_distinct_123 : (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_139) := by
  simpa only [nb074_alpha_dummy_138, nb074_alpha_dummy_139] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb074_fresh_124 (x : Var) : (nb074_alpha_dummy_140 x) ∉ (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb074_alpha_dummy_140] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb074_fresh_125 (x : Var) : (nb074_alpha_dummy_141 x) ∉ (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb074_alpha_dummy_141] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb074_fresh_126 (x : Var) : (nb074_alpha_dummy_142 x) ∉ (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb074_alpha_dummy_142] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb074_distinct_127 (x : Var) : (nb074_alpha_dummy_140 x) ≠ (nb074_alpha_dummy_141 x) := by
  simpa only [nb074_alpha_dummy_140, nb074_alpha_dummy_141] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb074_distinct_128 (x : Var) : (nb074_alpha_dummy_140 x) ≠ (nb074_alpha_dummy_142 x) := by
  simpa only [nb074_alpha_dummy_140, nb074_alpha_dummy_142] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb074_distinct_129 (x : Var) : (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_142 x) := by
  simpa only [nb074_alpha_dummy_141, nb074_alpha_dummy_142] using
    (freshVar_injective (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb074_fresh_130 : (nb074_alpha_dummy_149) ∉ (((Class.cv (nb074_alpha_dummy_138))).fv ∪ ((Class.cv (nb074_alpha_dummy_138))).fv) := by
  simpa only [nb074_alpha_dummy_149] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_138))).fv ∪ ((Class.cv (nb074_alpha_dummy_138))).fv) 0

theorem nb074_fresh_131 : (nb074_alpha_dummy_145) ∉ (((Class.cv (nb074_alpha_dummy_138))).fv ∪ ((Class.cv (nb074_alpha_dummy_139))).fv) := by
  simpa only [nb074_alpha_dummy_145] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_138))).fv ∪ ((Class.cv (nb074_alpha_dummy_139))).fv) 0

theorem nb074_fresh_132 : (nb074_alpha_dummy_151) ∉ (((Class.cv (nb074_alpha_dummy_139))).fv ∪ ((Class.cv (nb074_alpha_dummy_139))).fv) := by
  simpa only [nb074_alpha_dummy_151] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_139))).fv ∪ ((Class.cv (nb074_alpha_dummy_139))).fv) 0

theorem nb074_fresh_133 (x : Var) : (nb074_alpha_dummy_150 x) ∉ (((Class.cv (nb074_alpha_dummy_141 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_141 x))).fv) := by
  simpa only [nb074_alpha_dummy_150] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_141 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_141 x))).fv) 0

theorem nb074_fresh_134 (x : Var) : (nb074_alpha_dummy_146 x) ∉ (((Class.cv (nb074_alpha_dummy_141 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_142 x))).fv) := by
  simpa only [nb074_alpha_dummy_146] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_141 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_142 x))).fv) 0

theorem nb074_fresh_135 (x : Var) : (nb074_alpha_dummy_152 x) ∉ (((Class.cv (nb074_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_142 x))).fv) := by
  simpa only [nb074_alpha_dummy_152] using freshVar_not_mem (((Class.cv (nb074_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_142 x))).fv) 0

theorem nb074_fresh_136 (x : Var) : (nb074_alpha_dummy_083 x) ∉ (((Class.cv x)).fv) := by
  simpa only [nb074_alpha_dummy_083] using freshVar_not_mem (((Class.cv x)).fv) 0

theorem nb074_fresh_137 (x : Var) : (nb074_alpha_dummy_084 x) ∉ (((Class.cv x)).fv) := by
  simpa only [nb074_alpha_dummy_084] using freshVar_not_mem (((Class.cv x)).fv) 1

theorem nb074_distinct_138 (x : Var) : (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_084 x) := by
  simpa only [nb074_alpha_dummy_083, nb074_alpha_dummy_084] using
    (freshVar_injective (((Class.cv x)).fv) (i := 0) (j := 1) (by decide))

theorem nb074_fresh_139 (x : Var) : (nb074_alpha_dummy_007 x) ∉ (((Class.cv x)).fv ∪ ((Class.cv (nb074_alpha_dummy_002 x))).fv) := by
  simpa only [nb074_alpha_dummy_007] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb074_alpha_dummy_002 x))).fv) 0

theorem nb074_fresh_140 (x : Var) : (nb074_alpha_dummy_008 x) ∉ (((Class.cv x)).fv ∪ ((Class.cv (nb074_alpha_dummy_002 x))).fv) := by
  simpa only [nb074_alpha_dummy_008] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb074_alpha_dummy_002 x))).fv) 1

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
