import NominalAlphaCompactEnvFreshSupport002
import NominalAlphaTransport
import WPPCompactSourceSyntax
import WPPCompactSyntaxFVExplicit
import CoreFVSimp
import CompactSyntaxFVDisable
import ReplaySupport.Basic
import AlphaFocusedSupport
import FocusedFVPaths

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

noncomputable def nb055_alpha_dummy_000 : Var := (freshVar ((∅ : Finset Var)) 0)

noncomputable def nb055_alpha_dummy_001 : Var := (freshVar ((∅ : Finset Var)) 1)

noncomputable def nb055_alpha_dummy_002 : Var := (freshVar (({(nb055_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({(nb055_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_ccom (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv) 0)

noncomputable def nb055_alpha_dummy_003 (x : Var) (y : Var) : Var := (freshVar (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({y} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_ccom (Class.cv x) (Class.cv y))).fv) 0)

noncomputable def nb055_alpha_dummy_004 : Var := (freshVar (({(nb055_alpha_dummy_000)} : Finset Var) ∪ ({(nb055_alpha_dummy_001)} : Finset Var) ∪ ({(nb055_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb055_alpha_dummy_000)) (syn_cvv)) (Wff.classMem (Class.cv (nb055_alpha_dummy_001)) (syn_cvv))) (Wff.classEq (Class.cv (nb055_alpha_dummy_002)) (syn_ccom (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))))).fv) 0)

noncomputable def nb055_alpha_dummy_005 (x : Var) (y : Var) : Var := (freshVar (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb055_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv))) (Wff.classEq (Class.cv (nb055_alpha_dummy_003 x y)) (syn_ccom (Class.cv x) (Class.cv y))))).fv) 0)

noncomputable def nb055_alpha_dummy_006 : Var := (freshVar (((syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv ∪ ((Class.cv (nb055_alpha_dummy_002))).fv) 0)

noncomputable def nb055_alpha_dummy_007 : Var := (freshVar (((syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv ∪ ((Class.cv (nb055_alpha_dummy_002))).fv) 1)

noncomputable def nb055_alpha_dummy_008 (x : Var) (y : Var) : Var := (freshVar (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb055_alpha_dummy_003 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_009 (x : Var) (y : Var) : Var := (freshVar (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb055_alpha_dummy_003 x y))).fv) 1)

noncomputable def nb055_alpha_dummy_010 : Var := (freshVar (((syn_ccompl (Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001))) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cphi (Class.cv (nb055_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002)) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb055_alpha_dummy_011 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb055_alpha_dummy_012 : Var := (freshVar (((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001))) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cphi (Class.cv (nb055_alpha_dummy_007))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001))) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cphi (Class.cv (nb055_alpha_dummy_007))))))).fv) 0)

noncomputable def nb055_alpha_dummy_013 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))))).fv) 0)

noncomputable def nb055_alpha_dummy_014 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) 0)

noncomputable def nb055_alpha_dummy_015 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) 1)

noncomputable def nb055_alpha_dummy_016 (x : Var) (y : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

noncomputable def nb055_alpha_dummy_017 (x : Var) (y : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

noncomputable def nb055_alpha_dummy_018 : Var := (freshVar (((syn_ccompl (Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cphi (Class.cv (nb055_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb055_alpha_dummy_019 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb055_alpha_dummy_020 : Var := (freshVar (((Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cphi (Class.cv (nb055_alpha_dummy_015))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cphi (Class.cv (nb055_alpha_dummy_015))))))).fv) 0)

noncomputable def nb055_alpha_dummy_021 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))))))).fv) 0)

noncomputable def nb055_alpha_dummy_022 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_015))).fv) 0)

noncomputable def nb055_alpha_dummy_023 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_015))).fv) 1)

noncomputable def nb055_alpha_dummy_024 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_017 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_025 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_017 x y))).fv) 1)

noncomputable def nb055_alpha_dummy_026 : Var := (freshVar (((Wff.classMem (Class.cv (nb055_alpha_dummy_022)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_022)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_022))).fv) 0)

noncomputable def nb055_alpha_dummy_027 (x : Var) (y : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb055_alpha_dummy_024 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_024 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_024 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_028 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb055_alpha_dummy_029 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb055_alpha_dummy_030 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb055_alpha_dummy_031 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb055_alpha_dummy_032 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb055_alpha_dummy_033 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb055_alpha_dummy_034 : Var := (freshVar (((syn_cnin (Class.cv (nb055_alpha_dummy_029)) (Class.cv (nb055_alpha_dummy_030)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_029)) (Class.cv (nb055_alpha_dummy_030)))).fv) 0)

noncomputable def nb055_alpha_dummy_035 (x : Var) (y : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb055_alpha_dummy_032 x y)) (Class.cv (nb055_alpha_dummy_033 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_032 x y)) (Class.cv (nb055_alpha_dummy_033 x y)))).fv) 0)

noncomputable def nb055_alpha_dummy_036 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_029))).fv ∪ ((Class.cv (nb055_alpha_dummy_030))).fv) 0)

noncomputable def nb055_alpha_dummy_037 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_032 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_033 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_038 : Var := (freshVar (((syn_ccompl (Class.cv (nb055_alpha_dummy_029)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_030)))).fv) 0)

noncomputable def nb055_alpha_dummy_039 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb055_alpha_dummy_032 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_033 x y)))).fv) 0)

noncomputable def nb055_alpha_dummy_040 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_029))).fv ∪ ((Class.cv (nb055_alpha_dummy_029))).fv) 0)

noncomputable def nb055_alpha_dummy_041 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_032 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_032 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_042 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_030))).fv ∪ ((Class.cv (nb055_alpha_dummy_030))).fv) 0)

noncomputable def nb055_alpha_dummy_043 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_033 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_033 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_044 : Var := (freshVar (((Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb055_alpha_dummy_045 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb055_alpha_dummy_046 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_015))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb055_alpha_dummy_047 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb055_alpha_dummy_048 : Var := (freshVar (((syn_cphi (Class.cv (nb055_alpha_dummy_015)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_015)))).fv) 0)

noncomputable def nb055_alpha_dummy_049 (x : Var) (y : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))).fv) 0)

noncomputable def nb055_alpha_dummy_050 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_007))).fv) 0)

noncomputable def nb055_alpha_dummy_051 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_007))).fv) 1)

noncomputable def nb055_alpha_dummy_052 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_009 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_053 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_009 x y))).fv) 1)

noncomputable def nb055_alpha_dummy_054 : Var := (freshVar (((Wff.classMem (Class.cv (nb055_alpha_dummy_050)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_050)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_050))).fv) 0)

noncomputable def nb055_alpha_dummy_055 (x : Var) (y : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb055_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_052 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_052 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_056 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb055_alpha_dummy_057 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb055_alpha_dummy_058 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb055_alpha_dummy_059 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb055_alpha_dummy_060 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb055_alpha_dummy_061 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb055_alpha_dummy_062 : Var := (freshVar (((syn_cnin (Class.cv (nb055_alpha_dummy_057)) (Class.cv (nb055_alpha_dummy_058)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_057)) (Class.cv (nb055_alpha_dummy_058)))).fv) 0)

noncomputable def nb055_alpha_dummy_063 (x : Var) (y : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb055_alpha_dummy_060 x y)) (Class.cv (nb055_alpha_dummy_061 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_060 x y)) (Class.cv (nb055_alpha_dummy_061 x y)))).fv) 0)

noncomputable def nb055_alpha_dummy_064 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_057))).fv ∪ ((Class.cv (nb055_alpha_dummy_058))).fv) 0)

noncomputable def nb055_alpha_dummy_065 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_061 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_066 : Var := (freshVar (((syn_ccompl (Class.cv (nb055_alpha_dummy_057)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_058)))).fv) 0)

noncomputable def nb055_alpha_dummy_067 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb055_alpha_dummy_060 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_061 x y)))).fv) 0)

noncomputable def nb055_alpha_dummy_068 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_057))).fv ∪ ((Class.cv (nb055_alpha_dummy_057))).fv) 0)

noncomputable def nb055_alpha_dummy_069 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_060 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_070 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_058))).fv ∪ ((Class.cv (nb055_alpha_dummy_058))).fv) 0)

noncomputable def nb055_alpha_dummy_071 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_061 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_061 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_072 : Var := (freshVar (((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002)) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002)) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb055_alpha_dummy_073 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb055_alpha_dummy_074 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_007))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb055_alpha_dummy_075 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb055_alpha_dummy_076 : Var := (freshVar (((syn_cphi (Class.cv (nb055_alpha_dummy_007)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_007)))).fv) 0)

noncomputable def nb055_alpha_dummy_077 (x : Var) (y : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))).fv) 0)

noncomputable def nb055_alpha_dummy_078 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) 2)

noncomputable def nb055_alpha_dummy_079 (x : Var) (y : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 2)

noncomputable def nb055_alpha_dummy_080 : Var := (freshVar (({(nb055_alpha_dummy_014)} : Finset Var) ∪ ({(nb055_alpha_dummy_015)} : Finset Var) ∪ ((syn_wex (nb055_alpha_dummy_078) (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_014)) (Class.cv (nb055_alpha_dummy_001)) (Class.cv (nb055_alpha_dummy_078))) (syn_wbr (Class.cv (nb055_alpha_dummy_078)) (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_015)))))).fv) 0)

noncomputable def nb055_alpha_dummy_081 (x : Var) (y : Var) : Var := (freshVar (({(nb055_alpha_dummy_016 x y)} : Finset Var) ∪ ({(nb055_alpha_dummy_017 x y)} : Finset Var) ∪ ((syn_wex (nb055_alpha_dummy_079 x y) (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_016 x y)) (Class.cv y) (Class.cv (nb055_alpha_dummy_079 x y))) (syn_wbr (Class.cv (nb055_alpha_dummy_079 x y)) (Class.cv x) (Class.cv (nb055_alpha_dummy_017 x y)))))).fv) 0)

noncomputable def nb055_alpha_dummy_082 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) 0)

noncomputable def nb055_alpha_dummy_083 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) 1)

noncomputable def nb055_alpha_dummy_084 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_017 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_085 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_017 x y))).fv) 1)

noncomputable def nb055_alpha_dummy_086 : Var := (freshVar (((syn_ccompl (Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cphi (Class.cv (nb055_alpha_dummy_083)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb055_alpha_dummy_087 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb055_alpha_dummy_088 : Var := (freshVar (((Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cphi (Class.cv (nb055_alpha_dummy_083))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cphi (Class.cv (nb055_alpha_dummy_083))))))).fv) 0)

noncomputable def nb055_alpha_dummy_089 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))))))).fv) 0)

noncomputable def nb055_alpha_dummy_090 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_083))).fv) 0)

noncomputable def nb055_alpha_dummy_091 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_083))).fv) 1)

noncomputable def nb055_alpha_dummy_092 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_085 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_093 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_085 x y))).fv) 1)

noncomputable def nb055_alpha_dummy_094 : Var := (freshVar (((Wff.classMem (Class.cv (nb055_alpha_dummy_090)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_090)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_090))).fv) 0)

noncomputable def nb055_alpha_dummy_095 (x : Var) (y : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb055_alpha_dummy_092 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_092 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_092 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_096 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb055_alpha_dummy_097 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb055_alpha_dummy_098 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb055_alpha_dummy_099 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb055_alpha_dummy_100 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb055_alpha_dummy_101 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb055_alpha_dummy_102 : Var := (freshVar (((syn_cnin (Class.cv (nb055_alpha_dummy_097)) (Class.cv (nb055_alpha_dummy_098)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_097)) (Class.cv (nb055_alpha_dummy_098)))).fv) 0)

noncomputable def nb055_alpha_dummy_103 (x : Var) (y : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb055_alpha_dummy_100 x y)) (Class.cv (nb055_alpha_dummy_101 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_100 x y)) (Class.cv (nb055_alpha_dummy_101 x y)))).fv) 0)

noncomputable def nb055_alpha_dummy_104 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_097))).fv ∪ ((Class.cv (nb055_alpha_dummy_098))).fv) 0)

noncomputable def nb055_alpha_dummy_105 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_100 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_101 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_106 : Var := (freshVar (((syn_ccompl (Class.cv (nb055_alpha_dummy_097)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_098)))).fv) 0)

noncomputable def nb055_alpha_dummy_107 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb055_alpha_dummy_100 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_101 x y)))).fv) 0)

noncomputable def nb055_alpha_dummy_108 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_097))).fv ∪ ((Class.cv (nb055_alpha_dummy_097))).fv) 0)

noncomputable def nb055_alpha_dummy_109 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_100 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_100 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_110 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_098))).fv ∪ ((Class.cv (nb055_alpha_dummy_098))).fv) 0)

noncomputable def nb055_alpha_dummy_111 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_101 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_101 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_112 : Var := (freshVar (((Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb055_alpha_dummy_113 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb055_alpha_dummy_114 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_083))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb055_alpha_dummy_115 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb055_alpha_dummy_116 : Var := (freshVar (((syn_cphi (Class.cv (nb055_alpha_dummy_083)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_083)))).fv) 0)

noncomputable def nb055_alpha_dummy_117 (x : Var) (y : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))).fv) 0)

noncomputable def nb055_alpha_dummy_118 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_078))).fv) 0)

noncomputable def nb055_alpha_dummy_119 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_078))).fv) 1)

noncomputable def nb055_alpha_dummy_120 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_079 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_121 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_079 x y))).fv) 1)

noncomputable def nb055_alpha_dummy_122 : Var := (freshVar (((syn_ccompl (Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cphi (Class.cv (nb055_alpha_dummy_119)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb055_alpha_dummy_123 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb055_alpha_dummy_124 : Var := (freshVar (((Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cphi (Class.cv (nb055_alpha_dummy_119))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cphi (Class.cv (nb055_alpha_dummy_119))))))).fv) 0)

noncomputable def nb055_alpha_dummy_125 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))))))).fv) 0)

noncomputable def nb055_alpha_dummy_126 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_119))).fv) 0)

noncomputable def nb055_alpha_dummy_127 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_119))).fv) 1)

noncomputable def nb055_alpha_dummy_128 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_121 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_129 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_121 x y))).fv) 1)

noncomputable def nb055_alpha_dummy_130 : Var := (freshVar (((Wff.classMem (Class.cv (nb055_alpha_dummy_126)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_126)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_126))).fv) 0)

noncomputable def nb055_alpha_dummy_131 (x : Var) (y : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb055_alpha_dummy_128 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_128 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_128 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_132 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb055_alpha_dummy_133 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb055_alpha_dummy_134 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb055_alpha_dummy_135 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb055_alpha_dummy_136 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb055_alpha_dummy_137 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb055_alpha_dummy_138 : Var := (freshVar (((syn_cnin (Class.cv (nb055_alpha_dummy_133)) (Class.cv (nb055_alpha_dummy_134)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_133)) (Class.cv (nb055_alpha_dummy_134)))).fv) 0)

noncomputable def nb055_alpha_dummy_139 (x : Var) (y : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb055_alpha_dummy_136 x y)) (Class.cv (nb055_alpha_dummy_137 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_136 x y)) (Class.cv (nb055_alpha_dummy_137 x y)))).fv) 0)

noncomputable def nb055_alpha_dummy_140 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_133))).fv ∪ ((Class.cv (nb055_alpha_dummy_134))).fv) 0)

noncomputable def nb055_alpha_dummy_141 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_136 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_137 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_142 : Var := (freshVar (((syn_ccompl (Class.cv (nb055_alpha_dummy_133)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_134)))).fv) 0)

noncomputable def nb055_alpha_dummy_143 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb055_alpha_dummy_136 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_137 x y)))).fv) 0)

noncomputable def nb055_alpha_dummy_144 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_133))).fv ∪ ((Class.cv (nb055_alpha_dummy_133))).fv) 0)

noncomputable def nb055_alpha_dummy_145 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_136 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_136 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_146 : Var := (freshVar (((Class.cv (nb055_alpha_dummy_134))).fv ∪ ((Class.cv (nb055_alpha_dummy_134))).fv) 0)

noncomputable def nb055_alpha_dummy_147 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb055_alpha_dummy_137 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_137 x y))).fv) 0)

noncomputable def nb055_alpha_dummy_148 : Var := (freshVar (((Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb055_alpha_dummy_149 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))) (syn_csn (syn_c0c))))))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
