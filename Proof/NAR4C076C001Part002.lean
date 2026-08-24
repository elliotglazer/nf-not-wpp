import NAR4C076C001Part001

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

noncomputable def nb076_alpha_dummy_150 (g : Var) (b : Var) : Var := (freshVar (((Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb076_alpha_dummy_151 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_120))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb076_alpha_dummy_152 (g : Var) (b : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb076_alpha_dummy_153 : Var := (freshVar (((syn_cphi (Class.cv (nb076_alpha_dummy_120)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_120)))).fv) 0)

noncomputable def nb076_alpha_dummy_154 (g : Var) (b : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))).fv) 0)

noncomputable def nb076_alpha_dummy_155 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_082))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb076_alpha_dummy_156 (g : Var) (a : Var) (b : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb076_alpha_dummy_157 : Var := (freshVar (((syn_cphi (Class.cv (nb076_alpha_dummy_082)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_082)))).fv) 0)

noncomputable def nb076_alpha_dummy_158 (g : Var) (a : Var) (b : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))).fv) 0)

theorem nb076_fresh_000 : (nb076_alpha_dummy_075) ∉ (((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005)) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005)) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb076_alpha_dummy_075] using freshVar_not_mem (((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005)) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005)) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb076_fresh_001 : (nb076_alpha_dummy_015) ∉ (((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004))) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cphi (Class.cv (nb076_alpha_dummy_010))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004))) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cphi (Class.cv (nb076_alpha_dummy_010))))))).fv) := by
  simpa only [nb076_alpha_dummy_015] using freshVar_not_mem (((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004))) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cphi (Class.cv (nb076_alpha_dummy_010))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004))) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cphi (Class.cv (nb076_alpha_dummy_010))))))).fv) 0

theorem nb076_fresh_002 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_076 g m n a b) ∉ (((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb076_alpha_dummy_076] using freshVar_not_mem (((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb076_fresh_003 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_016 g m n a b) ∉ (((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))))).fv) := by
  simpa only [nb076_alpha_dummy_016] using freshVar_not_mem (((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))))).fv) 0

theorem nb076_fresh_004 : (nb076_alpha_dummy_023) ∉ (((Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cphi (Class.cv (nb076_alpha_dummy_018))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cphi (Class.cv (nb076_alpha_dummy_018))))))).fv) := by
  simpa only [nb076_alpha_dummy_023] using freshVar_not_mem (((Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cphi (Class.cv (nb076_alpha_dummy_018))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cphi (Class.cv (nb076_alpha_dummy_018))))))).fv) 0

theorem nb076_fresh_005 : (nb076_alpha_dummy_047) ∉ (((Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb076_alpha_dummy_047] using freshVar_not_mem (((Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb076_fresh_006 (m : Var) (n : Var) : (nb076_alpha_dummy_024 m n) ∉ (((Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))))).fv) := by
  simpa only [nb076_alpha_dummy_024] using freshVar_not_mem (((Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))))).fv) 0

theorem nb076_fresh_007 (m : Var) (n : Var) : (nb076_alpha_dummy_048 m n) ∉ (((Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb076_alpha_dummy_048] using freshVar_not_mem (((Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb076_fresh_008 : (nb076_alpha_dummy_087) ∉ (((Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000)) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cphi (Class.cv (nb076_alpha_dummy_082))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000)) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cphi (Class.cv (nb076_alpha_dummy_082))))))).fv) := by
  simpa only [nb076_alpha_dummy_087] using freshVar_not_mem (((Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000)) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cphi (Class.cv (nb076_alpha_dummy_082))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000)) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cphi (Class.cv (nb076_alpha_dummy_082))))))).fv) 0

theorem nb076_fresh_009 : (nb076_alpha_dummy_111) ∉ (((Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002))) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002))) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb076_alpha_dummy_111] using freshVar_not_mem (((Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002))) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002))) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb076_fresh_010 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_088 g a b) ∉ (((Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))))).fv) := by
  simpa only [nb076_alpha_dummy_088] using freshVar_not_mem (((Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))))).fv) 0

theorem nb076_fresh_011 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_112 g a b) ∉ (((Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g)) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g)) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb076_alpha_dummy_112] using freshVar_not_mem (((Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g)) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g)) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb076_fresh_012 : (nb076_alpha_dummy_125) ∉ (((Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cphi (Class.cv (nb076_alpha_dummy_120))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cphi (Class.cv (nb076_alpha_dummy_120))))))).fv) := by
  simpa only [nb076_alpha_dummy_125] using freshVar_not_mem (((Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cphi (Class.cv (nb076_alpha_dummy_120))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cphi (Class.cv (nb076_alpha_dummy_120))))))).fv) 0

theorem nb076_fresh_013 : (nb076_alpha_dummy_149) ∉ (((Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb076_alpha_dummy_149] using freshVar_not_mem (((Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb076_fresh_014 (g : Var) (b : Var) : (nb076_alpha_dummy_126 g b) ∉ (((Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))))).fv) := by
  simpa only [nb076_alpha_dummy_126] using freshVar_not_mem (((Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))))).fv) 0

theorem nb076_fresh_015 (g : Var) (b : Var) : (nb076_alpha_dummy_150 g b) ∉ (((Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb076_alpha_dummy_150] using freshVar_not_mem (((Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb076_fresh_016 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_083 g a b) ∉ (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv) := by
  simpa only [nb076_alpha_dummy_083] using freshVar_not_mem (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv) 0

theorem nb076_fresh_017 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_084 g a b) ∉ (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv) := by
  simpa only [nb076_alpha_dummy_084] using freshVar_not_mem (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv) 1

theorem nb076_distinct_018 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_083 g a b) ≠ (nb076_alpha_dummy_084 g a b) := by
  simpa only [nb076_alpha_dummy_083, nb076_alpha_dummy_084] using
    (freshVar_injective (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_019 : (nb076_alpha_dummy_081) ∉ (((Class.cv (nb076_alpha_dummy_000))).fv ∪ ((syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))).fv) := by
  simpa only [nb076_alpha_dummy_081] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_000))).fv ∪ ((syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))).fv) 0

theorem nb076_fresh_020 : (nb076_alpha_dummy_082) ∉ (((Class.cv (nb076_alpha_dummy_000))).fv ∪ ((syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))).fv) := by
  simpa only [nb076_alpha_dummy_082] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_000))).fv ∪ ((syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))).fv) 1

theorem nb076_distinct_021 : (nb076_alpha_dummy_081) ≠ (nb076_alpha_dummy_082) := by
  simpa only [nb076_alpha_dummy_081, nb076_alpha_dummy_082] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_000))).fv ∪ ((syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_022 : (nb076_alpha_dummy_113) ∉ (((Class.cv (nb076_alpha_dummy_001))).fv ∪ ((Class.cv (nb076_alpha_dummy_002))).fv) := by
  simpa only [nb076_alpha_dummy_113] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_001))).fv ∪ ((Class.cv (nb076_alpha_dummy_002))).fv) 0

theorem nb076_fresh_023 : (nb076_alpha_dummy_114) ∉ (((Class.cv (nb076_alpha_dummy_001))).fv ∪ ((Class.cv (nb076_alpha_dummy_002))).fv) := by
  simpa only [nb076_alpha_dummy_114] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_001))).fv ∪ ((Class.cv (nb076_alpha_dummy_002))).fv) 1

theorem nb076_distinct_024 : (nb076_alpha_dummy_113) ≠ (nb076_alpha_dummy_114) := by
  simpa only [nb076_alpha_dummy_113, nb076_alpha_dummy_114] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_001))).fv ∪ ((Class.cv (nb076_alpha_dummy_002))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_025 : (nb076_alpha_dummy_017) ∉ (((Class.cv (nb076_alpha_dummy_003))).fv ∪ ((Class.cv (nb076_alpha_dummy_004))).fv) := by
  simpa only [nb076_alpha_dummy_017] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_003))).fv ∪ ((Class.cv (nb076_alpha_dummy_004))).fv) 0

theorem nb076_fresh_026 : (nb076_alpha_dummy_018) ∉ (((Class.cv (nb076_alpha_dummy_003))).fv ∪ ((Class.cv (nb076_alpha_dummy_004))).fv) := by
  simpa only [nb076_alpha_dummy_018] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_003))).fv ∪ ((Class.cv (nb076_alpha_dummy_004))).fv) 1

theorem nb076_distinct_027 : (nb076_alpha_dummy_017) ≠ (nb076_alpha_dummy_018) := by
  simpa only [nb076_alpha_dummy_017, nb076_alpha_dummy_018] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_003))).fv ∪ ((Class.cv (nb076_alpha_dummy_004))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_028 : (nb076_alpha_dummy_053) ∉ (((Class.cv (nb076_alpha_dummy_010))).fv) := by
  simpa only [nb076_alpha_dummy_053] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_010))).fv) 0

theorem nb076_fresh_029 : (nb076_alpha_dummy_054) ∉ (((Class.cv (nb076_alpha_dummy_010))).fv) := by
  simpa only [nb076_alpha_dummy_054] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_010))).fv) 1

theorem nb076_distinct_030 : (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_054) := by
  simpa only [nb076_alpha_dummy_053, nb076_alpha_dummy_054] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_010))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_031 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_055 g m n a b) ∉ (((Class.cv (nb076_alpha_dummy_012 g m n a b))).fv) := by
  simpa only [nb076_alpha_dummy_055] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_012 g m n a b))).fv) 0

theorem nb076_fresh_032 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_056 g m n a b) ∉ (((Class.cv (nb076_alpha_dummy_012 g m n a b))).fv) := by
  simpa only [nb076_alpha_dummy_056] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_012 g m n a b))).fv) 1

theorem nb076_distinct_033 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_055 g m n a b) ≠ (nb076_alpha_dummy_056 g m n a b) := by
  simpa only [nb076_alpha_dummy_055, nb076_alpha_dummy_056] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_012 g m n a b))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_034 : (nb076_alpha_dummy_025) ∉ (((Class.cv (nb076_alpha_dummy_018))).fv) := by
  simpa only [nb076_alpha_dummy_025] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_018))).fv) 0

theorem nb076_fresh_035 : (nb076_alpha_dummy_026) ∉ (((Class.cv (nb076_alpha_dummy_018))).fv) := by
  simpa only [nb076_alpha_dummy_026] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_018))).fv) 1

theorem nb076_distinct_036 : (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_026) := by
  simpa only [nb076_alpha_dummy_025, nb076_alpha_dummy_026] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_018))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_037 (m : Var) (n : Var) : (nb076_alpha_dummy_027 m n) ∉ (((Class.cv (nb076_alpha_dummy_020 m n))).fv) := by
  simpa only [nb076_alpha_dummy_027] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_020 m n))).fv) 0

theorem nb076_fresh_038 (m : Var) (n : Var) : (nb076_alpha_dummy_028 m n) ∉ (((Class.cv (nb076_alpha_dummy_020 m n))).fv) := by
  simpa only [nb076_alpha_dummy_028] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_020 m n))).fv) 1

theorem nb076_distinct_039 (m : Var) (n : Var) : (nb076_alpha_dummy_027 m n) ≠ (nb076_alpha_dummy_028 m n) := by
  simpa only [nb076_alpha_dummy_027, nb076_alpha_dummy_028] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_020 m n))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_040 : (nb076_alpha_dummy_031) ∉ (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb076_alpha_dummy_031] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) 0

theorem nb076_fresh_041 : (nb076_alpha_dummy_032) ∉ (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb076_alpha_dummy_032] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) 1

theorem nb076_fresh_042 : (nb076_alpha_dummy_033) ∉ (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb076_alpha_dummy_033] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) 2

theorem nb076_distinct_043 : (nb076_alpha_dummy_031) ≠ (nb076_alpha_dummy_032) := by
  simpa only [nb076_alpha_dummy_031, nb076_alpha_dummy_032] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb076_distinct_044 : (nb076_alpha_dummy_031) ≠ (nb076_alpha_dummy_033) := by
  simpa only [nb076_alpha_dummy_031, nb076_alpha_dummy_033] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb076_distinct_045 : (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_033) := by
  simpa only [nb076_alpha_dummy_032, nb076_alpha_dummy_033] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb076_fresh_046 (m : Var) (n : Var) : (nb076_alpha_dummy_034 m n) ∉ (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb076_alpha_dummy_034] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) 0

theorem nb076_fresh_047 (m : Var) (n : Var) : (nb076_alpha_dummy_035 m n) ∉ (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb076_alpha_dummy_035] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) 1

theorem nb076_fresh_048 (m : Var) (n : Var) : (nb076_alpha_dummy_036 m n) ∉ (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb076_alpha_dummy_036] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) 2

theorem nb076_distinct_049 (m : Var) (n : Var) : (nb076_alpha_dummy_034 m n) ≠ (nb076_alpha_dummy_035 m n) := by
  simpa only [nb076_alpha_dummy_034, nb076_alpha_dummy_035] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb076_distinct_050 (m : Var) (n : Var) : (nb076_alpha_dummy_034 m n) ≠ (nb076_alpha_dummy_036 m n) := by
  simpa only [nb076_alpha_dummy_034, nb076_alpha_dummy_036] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb076_distinct_051 (m : Var) (n : Var) : (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_036 m n) := by
  simpa only [nb076_alpha_dummy_035, nb076_alpha_dummy_036] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb076_fresh_052 : (nb076_alpha_dummy_043) ∉ (((Class.cv (nb076_alpha_dummy_032))).fv ∪ ((Class.cv (nb076_alpha_dummy_032))).fv) := by
  simpa only [nb076_alpha_dummy_043] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_032))).fv ∪ ((Class.cv (nb076_alpha_dummy_032))).fv) 0

theorem nb076_fresh_053 : (nb076_alpha_dummy_039) ∉ (((Class.cv (nb076_alpha_dummy_032))).fv ∪ ((Class.cv (nb076_alpha_dummy_033))).fv) := by
  simpa only [nb076_alpha_dummy_039] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_032))).fv ∪ ((Class.cv (nb076_alpha_dummy_033))).fv) 0

theorem nb076_fresh_054 : (nb076_alpha_dummy_045) ∉ (((Class.cv (nb076_alpha_dummy_033))).fv ∪ ((Class.cv (nb076_alpha_dummy_033))).fv) := by
  simpa only [nb076_alpha_dummy_045] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_033))).fv ∪ ((Class.cv (nb076_alpha_dummy_033))).fv) 0

theorem nb076_fresh_055 (m : Var) (n : Var) : (nb076_alpha_dummy_044 m n) ∉ (((Class.cv (nb076_alpha_dummy_035 m n))).fv ∪ ((Class.cv (nb076_alpha_dummy_035 m n))).fv) := by
  simpa only [nb076_alpha_dummy_044] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_035 m n))).fv ∪ ((Class.cv (nb076_alpha_dummy_035 m n))).fv) 0

theorem nb076_fresh_056 (m : Var) (n : Var) : (nb076_alpha_dummy_040 m n) ∉ (((Class.cv (nb076_alpha_dummy_035 m n))).fv ∪ ((Class.cv (nb076_alpha_dummy_036 m n))).fv) := by
  simpa only [nb076_alpha_dummy_040] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_035 m n))).fv ∪ ((Class.cv (nb076_alpha_dummy_036 m n))).fv) 0

theorem nb076_fresh_057 (m : Var) (n : Var) : (nb076_alpha_dummy_046 m n) ∉ (((Class.cv (nb076_alpha_dummy_036 m n))).fv ∪ ((Class.cv (nb076_alpha_dummy_036 m n))).fv) := by
  simpa only [nb076_alpha_dummy_046] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_036 m n))).fv ∪ ((Class.cv (nb076_alpha_dummy_036 m n))).fv) 0

theorem nb076_fresh_058 : (nb076_alpha_dummy_059) ∉ (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb076_alpha_dummy_059] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 0

theorem nb076_fresh_059 : (nb076_alpha_dummy_060) ∉ (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb076_alpha_dummy_060] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 1

theorem nb076_fresh_060 : (nb076_alpha_dummy_061) ∉ (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb076_alpha_dummy_061] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 2

theorem nb076_distinct_061 : (nb076_alpha_dummy_059) ≠ (nb076_alpha_dummy_060) := by
  simpa only [nb076_alpha_dummy_059, nb076_alpha_dummy_060] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb076_distinct_062 : (nb076_alpha_dummy_059) ≠ (nb076_alpha_dummy_061) := by
  simpa only [nb076_alpha_dummy_059, nb076_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb076_distinct_063 : (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_061) := by
  simpa only [nb076_alpha_dummy_060, nb076_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb076_fresh_064 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_062 g m n a b) ∉ (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb076_alpha_dummy_062] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) 0

theorem nb076_fresh_065 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_063 g m n a b) ∉ (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb076_alpha_dummy_063] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) 1

theorem nb076_fresh_066 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_064 g m n a b) ∉ (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb076_alpha_dummy_064] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) 2

theorem nb076_distinct_067 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_062 g m n a b) ≠ (nb076_alpha_dummy_063 g m n a b) := by
  simpa only [nb076_alpha_dummy_062, nb076_alpha_dummy_063] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb076_distinct_068 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_062 g m n a b) ≠ (nb076_alpha_dummy_064 g m n a b) := by
  simpa only [nb076_alpha_dummy_062, nb076_alpha_dummy_064] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb076_distinct_069 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_064 g m n a b) := by
  simpa only [nb076_alpha_dummy_063, nb076_alpha_dummy_064] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb076_fresh_070 : (nb076_alpha_dummy_071) ∉ (((Class.cv (nb076_alpha_dummy_060))).fv ∪ ((Class.cv (nb076_alpha_dummy_060))).fv) := by
  simpa only [nb076_alpha_dummy_071] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_060))).fv ∪ ((Class.cv (nb076_alpha_dummy_060))).fv) 0

theorem nb076_fresh_071 : (nb076_alpha_dummy_067) ∉ (((Class.cv (nb076_alpha_dummy_060))).fv ∪ ((Class.cv (nb076_alpha_dummy_061))).fv) := by
  simpa only [nb076_alpha_dummy_067] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_060))).fv ∪ ((Class.cv (nb076_alpha_dummy_061))).fv) 0

theorem nb076_fresh_072 : (nb076_alpha_dummy_073) ∉ (((Class.cv (nb076_alpha_dummy_061))).fv ∪ ((Class.cv (nb076_alpha_dummy_061))).fv) := by
  simpa only [nb076_alpha_dummy_073] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_061))).fv ∪ ((Class.cv (nb076_alpha_dummy_061))).fv) 0

theorem nb076_fresh_073 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_072 g m n a b) ∉ (((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv) := by
  simpa only [nb076_alpha_dummy_072] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv) 0

theorem nb076_fresh_074 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_068 g m n a b) ∉ (((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv) := by
  simpa only [nb076_alpha_dummy_068] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv) 0

theorem nb076_fresh_075 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_074 g m n a b) ∉ (((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv) := by
  simpa only [nb076_alpha_dummy_074] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv) 0

theorem nb076_fresh_076 : (nb076_alpha_dummy_089) ∉ (((Class.cv (nb076_alpha_dummy_082))).fv) := by
  simpa only [nb076_alpha_dummy_089] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_082))).fv) 0

theorem nb076_fresh_077 : (nb076_alpha_dummy_090) ∉ (((Class.cv (nb076_alpha_dummy_082))).fv) := by
  simpa only [nb076_alpha_dummy_090] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_082))).fv) 1

theorem nb076_distinct_078 : (nb076_alpha_dummy_089) ≠ (nb076_alpha_dummy_090) := by
  simpa only [nb076_alpha_dummy_089, nb076_alpha_dummy_090] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_082))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_079 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_091 g a b) ∉ (((Class.cv (nb076_alpha_dummy_084 g a b))).fv) := by
  simpa only [nb076_alpha_dummy_091] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_084 g a b))).fv) 0

theorem nb076_fresh_080 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_092 g a b) ∉ (((Class.cv (nb076_alpha_dummy_084 g a b))).fv) := by
  simpa only [nb076_alpha_dummy_092] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_084 g a b))).fv) 1

theorem nb076_distinct_081 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_091 g a b) ≠ (nb076_alpha_dummy_092 g a b) := by
  simpa only [nb076_alpha_dummy_091, nb076_alpha_dummy_092] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_084 g a b))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_082 : (nb076_alpha_dummy_095) ∉ (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb076_alpha_dummy_095] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) 0

theorem nb076_fresh_083 : (nb076_alpha_dummy_096) ∉ (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb076_alpha_dummy_096] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) 1

theorem nb076_fresh_084 : (nb076_alpha_dummy_097) ∉ (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb076_alpha_dummy_097] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) 2

theorem nb076_distinct_085 : (nb076_alpha_dummy_095) ≠ (nb076_alpha_dummy_096) := by
  simpa only [nb076_alpha_dummy_095, nb076_alpha_dummy_096] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb076_distinct_086 : (nb076_alpha_dummy_095) ≠ (nb076_alpha_dummy_097) := by
  simpa only [nb076_alpha_dummy_095, nb076_alpha_dummy_097] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb076_distinct_087 : (nb076_alpha_dummy_096) ≠ (nb076_alpha_dummy_097) := by
  simpa only [nb076_alpha_dummy_096, nb076_alpha_dummy_097] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb076_fresh_088 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_098 g a b) ∉ (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb076_alpha_dummy_098] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) 0

theorem nb076_fresh_089 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_099 g a b) ∉ (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb076_alpha_dummy_099] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) 1

theorem nb076_fresh_090 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_100 g a b) ∉ (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb076_alpha_dummy_100] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) 2

theorem nb076_distinct_091 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_098 g a b) ≠ (nb076_alpha_dummy_099 g a b) := by
  simpa only [nb076_alpha_dummy_098, nb076_alpha_dummy_099] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb076_distinct_092 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_098 g a b) ≠ (nb076_alpha_dummy_100 g a b) := by
  simpa only [nb076_alpha_dummy_098, nb076_alpha_dummy_100] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb076_distinct_093 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_099 g a b) ≠ (nb076_alpha_dummy_100 g a b) := by
  simpa only [nb076_alpha_dummy_099, nb076_alpha_dummy_100] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb076_fresh_094 : (nb076_alpha_dummy_107) ∉ (((Class.cv (nb076_alpha_dummy_096))).fv ∪ ((Class.cv (nb076_alpha_dummy_096))).fv) := by
  simpa only [nb076_alpha_dummy_107] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_096))).fv ∪ ((Class.cv (nb076_alpha_dummy_096))).fv) 0

theorem nb076_fresh_095 : (nb076_alpha_dummy_103) ∉ (((Class.cv (nb076_alpha_dummy_096))).fv ∪ ((Class.cv (nb076_alpha_dummy_097))).fv) := by
  simpa only [nb076_alpha_dummy_103] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_096))).fv ∪ ((Class.cv (nb076_alpha_dummy_097))).fv) 0

theorem nb076_fresh_096 : (nb076_alpha_dummy_109) ∉ (((Class.cv (nb076_alpha_dummy_097))).fv ∪ ((Class.cv (nb076_alpha_dummy_097))).fv) := by
  simpa only [nb076_alpha_dummy_109] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_097))).fv ∪ ((Class.cv (nb076_alpha_dummy_097))).fv) 0

theorem nb076_fresh_097 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_108 g a b) ∉ (((Class.cv (nb076_alpha_dummy_099 g a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_099 g a b))).fv) := by
  simpa only [nb076_alpha_dummy_108] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_099 g a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_099 g a b))).fv) 0

theorem nb076_fresh_098 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_104 g a b) ∉ (((Class.cv (nb076_alpha_dummy_099 g a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_100 g a b))).fv) := by
  simpa only [nb076_alpha_dummy_104] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_099 g a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_100 g a b))).fv) 0

theorem nb076_fresh_099 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_110 g a b) ∉ (((Class.cv (nb076_alpha_dummy_100 g a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_100 g a b))).fv) := by
  simpa only [nb076_alpha_dummy_110] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_100 g a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_100 g a b))).fv) 0

theorem nb076_fresh_100 : (nb076_alpha_dummy_119) ∉ (((Class.cv (nb076_alpha_dummy_113))).fv ∪ ((Class.cv (nb076_alpha_dummy_114))).fv) := by
  simpa only [nb076_alpha_dummy_119] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_113))).fv ∪ ((Class.cv (nb076_alpha_dummy_114))).fv) 0

theorem nb076_fresh_101 : (nb076_alpha_dummy_120) ∉ (((Class.cv (nb076_alpha_dummy_113))).fv ∪ ((Class.cv (nb076_alpha_dummy_114))).fv) := by
  simpa only [nb076_alpha_dummy_120] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_113))).fv ∪ ((Class.cv (nb076_alpha_dummy_114))).fv) 1

theorem nb076_distinct_102 : (nb076_alpha_dummy_119) ≠ (nb076_alpha_dummy_120) := by
  simpa only [nb076_alpha_dummy_119, nb076_alpha_dummy_120] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_113))).fv ∪ ((Class.cv (nb076_alpha_dummy_114))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_103 (g : Var) (b : Var) : (nb076_alpha_dummy_121 g b) ∉ (((Class.cv (nb076_alpha_dummy_115 g b))).fv ∪ ((Class.cv (nb076_alpha_dummy_116 g b))).fv) := by
  simpa only [nb076_alpha_dummy_121] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_115 g b))).fv ∪ ((Class.cv (nb076_alpha_dummy_116 g b))).fv) 0

theorem nb076_fresh_104 (g : Var) (b : Var) : (nb076_alpha_dummy_122 g b) ∉ (((Class.cv (nb076_alpha_dummy_115 g b))).fv ∪ ((Class.cv (nb076_alpha_dummy_116 g b))).fv) := by
  simpa only [nb076_alpha_dummy_122] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_115 g b))).fv ∪ ((Class.cv (nb076_alpha_dummy_116 g b))).fv) 1

theorem nb076_distinct_105 (g : Var) (b : Var) : (nb076_alpha_dummy_121 g b) ≠ (nb076_alpha_dummy_122 g b) := by
  simpa only [nb076_alpha_dummy_121, nb076_alpha_dummy_122] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_115 g b))).fv ∪ ((Class.cv (nb076_alpha_dummy_116 g b))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_106 : (nb076_alpha_dummy_127) ∉ (((Class.cv (nb076_alpha_dummy_120))).fv) := by
  simpa only [nb076_alpha_dummy_127] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_120))).fv) 0

theorem nb076_fresh_107 : (nb076_alpha_dummy_128) ∉ (((Class.cv (nb076_alpha_dummy_120))).fv) := by
  simpa only [nb076_alpha_dummy_128] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_120))).fv) 1

theorem nb076_distinct_108 : (nb076_alpha_dummy_127) ≠ (nb076_alpha_dummy_128) := by
  simpa only [nb076_alpha_dummy_127, nb076_alpha_dummy_128] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_120))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_109 (g : Var) (b : Var) : (nb076_alpha_dummy_129 g b) ∉ (((Class.cv (nb076_alpha_dummy_122 g b))).fv) := by
  simpa only [nb076_alpha_dummy_129] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_122 g b))).fv) 0

theorem nb076_fresh_110 (g : Var) (b : Var) : (nb076_alpha_dummy_130 g b) ∉ (((Class.cv (nb076_alpha_dummy_122 g b))).fv) := by
  simpa only [nb076_alpha_dummy_130] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_122 g b))).fv) 1

theorem nb076_distinct_111 (g : Var) (b : Var) : (nb076_alpha_dummy_129 g b) ≠ (nb076_alpha_dummy_130 g b) := by
  simpa only [nb076_alpha_dummy_129, nb076_alpha_dummy_130] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_122 g b))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_112 : (nb076_alpha_dummy_133) ∉ (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb076_alpha_dummy_133] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) 0

theorem nb076_fresh_113 : (nb076_alpha_dummy_134) ∉ (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb076_alpha_dummy_134] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) 1

theorem nb076_fresh_114 : (nb076_alpha_dummy_135) ∉ (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb076_alpha_dummy_135] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) 2

theorem nb076_distinct_115 : (nb076_alpha_dummy_133) ≠ (nb076_alpha_dummy_134) := by
  simpa only [nb076_alpha_dummy_133, nb076_alpha_dummy_134] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb076_distinct_116 : (nb076_alpha_dummy_133) ≠ (nb076_alpha_dummy_135) := by
  simpa only [nb076_alpha_dummy_133, nb076_alpha_dummy_135] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb076_distinct_117 : (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_135) := by
  simpa only [nb076_alpha_dummy_134, nb076_alpha_dummy_135] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb076_fresh_118 (g : Var) (b : Var) : (nb076_alpha_dummy_136 g b) ∉ (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb076_alpha_dummy_136] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) 0

theorem nb076_fresh_119 (g : Var) (b : Var) : (nb076_alpha_dummy_137 g b) ∉ (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb076_alpha_dummy_137] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) 1

theorem nb076_fresh_120 (g : Var) (b : Var) : (nb076_alpha_dummy_138 g b) ∉ (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb076_alpha_dummy_138] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) 2

theorem nb076_distinct_121 (g : Var) (b : Var) : (nb076_alpha_dummy_136 g b) ≠ (nb076_alpha_dummy_137 g b) := by
  simpa only [nb076_alpha_dummy_136, nb076_alpha_dummy_137] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb076_distinct_122 (g : Var) (b : Var) : (nb076_alpha_dummy_136 g b) ≠ (nb076_alpha_dummy_138 g b) := by
  simpa only [nb076_alpha_dummy_136, nb076_alpha_dummy_138] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb076_distinct_123 (g : Var) (b : Var) : (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_138 g b) := by
  simpa only [nb076_alpha_dummy_137, nb076_alpha_dummy_138] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb076_fresh_124 : (nb076_alpha_dummy_145) ∉ (((Class.cv (nb076_alpha_dummy_134))).fv ∪ ((Class.cv (nb076_alpha_dummy_134))).fv) := by
  simpa only [nb076_alpha_dummy_145] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_134))).fv ∪ ((Class.cv (nb076_alpha_dummy_134))).fv) 0

theorem nb076_fresh_125 : (nb076_alpha_dummy_141) ∉ (((Class.cv (nb076_alpha_dummy_134))).fv ∪ ((Class.cv (nb076_alpha_dummy_135))).fv) := by
  simpa only [nb076_alpha_dummy_141] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_134))).fv ∪ ((Class.cv (nb076_alpha_dummy_135))).fv) 0

theorem nb076_fresh_126 : (nb076_alpha_dummy_147) ∉ (((Class.cv (nb076_alpha_dummy_135))).fv ∪ ((Class.cv (nb076_alpha_dummy_135))).fv) := by
  simpa only [nb076_alpha_dummy_147] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_135))).fv ∪ ((Class.cv (nb076_alpha_dummy_135))).fv) 0

theorem nb076_fresh_127 (g : Var) (b : Var) : (nb076_alpha_dummy_146 g b) ∉ (((Class.cv (nb076_alpha_dummy_137 g b))).fv ∪ ((Class.cv (nb076_alpha_dummy_137 g b))).fv) := by
  simpa only [nb076_alpha_dummy_146] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_137 g b))).fv ∪ ((Class.cv (nb076_alpha_dummy_137 g b))).fv) 0

theorem nb076_fresh_128 (g : Var) (b : Var) : (nb076_alpha_dummy_142 g b) ∉ (((Class.cv (nb076_alpha_dummy_137 g b))).fv ∪ ((Class.cv (nb076_alpha_dummy_138 g b))).fv) := by
  simpa only [nb076_alpha_dummy_142] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_137 g b))).fv ∪ ((Class.cv (nb076_alpha_dummy_138 g b))).fv) 0

theorem nb076_fresh_129 (g : Var) (b : Var) : (nb076_alpha_dummy_148 g b) ∉ (((Class.cv (nb076_alpha_dummy_138 g b))).fv ∪ ((Class.cv (nb076_alpha_dummy_138 g b))).fv) := by
  simpa only [nb076_alpha_dummy_148] using freshVar_not_mem (((Class.cv (nb076_alpha_dummy_138 g b))).fv ∪ ((Class.cv (nb076_alpha_dummy_138 g b))).fv) 0

theorem nb076_fresh_130 (g : Var) (b : Var) : (nb076_alpha_dummy_115 g b) ∉ (((Class.cv b)).fv ∪ ((Class.cv g)).fv) := by
  simpa only [nb076_alpha_dummy_115] using freshVar_not_mem (((Class.cv b)).fv ∪ ((Class.cv g)).fv) 0

theorem nb076_fresh_131 (g : Var) (b : Var) : (nb076_alpha_dummy_116 g b) ∉ (((Class.cv b)).fv ∪ ((Class.cv g)).fv) := by
  simpa only [nb076_alpha_dummy_116] using freshVar_not_mem (((Class.cv b)).fv ∪ ((Class.cv g)).fv) 1

theorem nb076_distinct_132 (g : Var) (b : Var) : (nb076_alpha_dummy_115 g b) ≠ (nb076_alpha_dummy_116 g b) := by
  simpa only [nb076_alpha_dummy_115, nb076_alpha_dummy_116] using
    (freshVar_injective (((Class.cv b)).fv ∪ ((Class.cv g)).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_133 (m : Var) (n : Var) : (nb076_alpha_dummy_019 m n) ∉ (((Class.cv m)).fv ∪ ((Class.cv n)).fv) := by
  simpa only [nb076_alpha_dummy_019] using freshVar_not_mem (((Class.cv m)).fv ∪ ((Class.cv n)).fv) 0

theorem nb076_fresh_134 (m : Var) (n : Var) : (nb076_alpha_dummy_020 m n) ∉ (((Class.cv m)).fv ∪ ((Class.cv n)).fv) := by
  simpa only [nb076_alpha_dummy_020] using freshVar_not_mem (((Class.cv m)).fv ∪ ((Class.cv n)).fv) 1

theorem nb076_distinct_135 (m : Var) (n : Var) : (nb076_alpha_dummy_019 m n) ≠ (nb076_alpha_dummy_020 m n) := by
  simpa only [nb076_alpha_dummy_019, nb076_alpha_dummy_020] using
    (freshVar_injective (((Class.cv m)).fv ∪ ((Class.cv n)).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_136 : (nb076_alpha_dummy_029) ∉ (((Wff.classMem (Class.cv (nb076_alpha_dummy_025)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_025)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_025))).fv) := by
  simpa only [nb076_alpha_dummy_029] using freshVar_not_mem (((Wff.classMem (Class.cv (nb076_alpha_dummy_025)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_025)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_025))).fv) 0

theorem nb076_fresh_137 (m : Var) (n : Var) : (nb076_alpha_dummy_030 m n) ∉ (((Wff.classMem (Class.cv (nb076_alpha_dummy_027 m n)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_027 m n)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_027 m n))).fv) := by
  simpa only [nb076_alpha_dummy_030] using freshVar_not_mem (((Wff.classMem (Class.cv (nb076_alpha_dummy_027 m n)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_027 m n)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_027 m n))).fv) 0

theorem nb076_fresh_138 : (nb076_alpha_dummy_057) ∉ (((Wff.classMem (Class.cv (nb076_alpha_dummy_053)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_053)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_053))).fv) := by
  simpa only [nb076_alpha_dummy_057] using freshVar_not_mem (((Wff.classMem (Class.cv (nb076_alpha_dummy_053)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_053)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_053))).fv) 0

theorem nb076_fresh_139 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_058 g m n a b) ∉ (((Wff.classMem (Class.cv (nb076_alpha_dummy_055 g m n a b)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_055 g m n a b)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv) := by
  simpa only [nb076_alpha_dummy_058] using freshVar_not_mem (((Wff.classMem (Class.cv (nb076_alpha_dummy_055 g m n a b)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_055 g m n a b)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv) 0

theorem nb076_fresh_140 : (nb076_alpha_dummy_093) ∉ (((Wff.classMem (Class.cv (nb076_alpha_dummy_089)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_089)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_089))).fv) := by
  simpa only [nb076_alpha_dummy_093] using freshVar_not_mem (((Wff.classMem (Class.cv (nb076_alpha_dummy_089)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_089)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_089))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
