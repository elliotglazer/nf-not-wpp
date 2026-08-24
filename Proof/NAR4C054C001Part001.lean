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

noncomputable def nb054_alpha_dummy_000 : Var := (freshVar ((∅ : Finset Var)) 0)

noncomputable def nb054_alpha_dummy_001 : Var := (freshVar ((∅ : Finset Var)) 1)

noncomputable def nb054_alpha_dummy_002 : Var := (freshVar (({(nb054_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({(nb054_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cplc (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001)))).fv) 0)

noncomputable def nb054_alpha_dummy_003 (x : Var) (y : Var) : Var := (freshVar (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({y} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cplc (Class.cv x) (Class.cv y))).fv) 0)

noncomputable def nb054_alpha_dummy_004 : Var := (freshVar (({(nb054_alpha_dummy_000)} : Finset Var) ∪ ({(nb054_alpha_dummy_001)} : Finset Var) ∪ ({(nb054_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb054_alpha_dummy_000)) (syn_cvv)) (Wff.classMem (Class.cv (nb054_alpha_dummy_001)) (syn_cvv))) (Wff.classEq (Class.cv (nb054_alpha_dummy_002)) (syn_cplc (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001)))))).fv) 0)

noncomputable def nb054_alpha_dummy_005 (x : Var) (y : Var) : Var := (freshVar (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb054_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv))) (Wff.classEq (Class.cv (nb054_alpha_dummy_003 x y)) (syn_cplc (Class.cv x) (Class.cv y))))).fv) 0)

noncomputable def nb054_alpha_dummy_006 : Var := (freshVar (((syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001)))).fv ∪ ((Class.cv (nb054_alpha_dummy_002))).fv) 0)

noncomputable def nb054_alpha_dummy_007 : Var := (freshVar (((syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001)))).fv ∪ ((Class.cv (nb054_alpha_dummy_002))).fv) 1)

noncomputable def nb054_alpha_dummy_008 (x : Var) (y : Var) : Var := (freshVar (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb054_alpha_dummy_003 x y))).fv) 0)

noncomputable def nb054_alpha_dummy_009 (x : Var) (y : Var) : Var := (freshVar (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb054_alpha_dummy_003 x y))).fv) 1)

noncomputable def nb054_alpha_dummy_010 : Var := (freshVar (((syn_ccompl (Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001))) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cphi (Class.cv (nb054_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl (Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (Class.cv (nb054_alpha_dummy_002)) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_007))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb054_alpha_dummy_011 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (Class.cv (nb054_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb054_alpha_dummy_012 : Var := (freshVar (((Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001))) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cphi (Class.cv (nb054_alpha_dummy_007))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001))) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cphi (Class.cv (nb054_alpha_dummy_007))))))).fv) 0)

noncomputable def nb054_alpha_dummy_013 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))))))).fv) 0)

noncomputable def nb054_alpha_dummy_014 : Var := (freshVar (((Class.cv (nb054_alpha_dummy_000))).fv ∪ ((Class.cv (nb054_alpha_dummy_001))).fv) 0)

noncomputable def nb054_alpha_dummy_015 : Var := (freshVar (((Class.cv (nb054_alpha_dummy_000))).fv ∪ ((Class.cv (nb054_alpha_dummy_001))).fv) 1)

noncomputable def nb054_alpha_dummy_016 (x : Var) (y : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

noncomputable def nb054_alpha_dummy_017 (x : Var) (y : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

noncomputable def nb054_alpha_dummy_018 : Var := (freshVar (((syn_ccompl (Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_000)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cphi (Class.cv (nb054_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl (Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_001)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_015))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb054_alpha_dummy_019 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb054_alpha_dummy_020 : Var := (freshVar (((Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_000)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cphi (Class.cv (nb054_alpha_dummy_015))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_000)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cphi (Class.cv (nb054_alpha_dummy_015))))))).fv) 0)

noncomputable def nb054_alpha_dummy_021 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))))))).fv) 0)

noncomputable def nb054_alpha_dummy_022 : Var := (freshVar (((Class.cv (nb054_alpha_dummy_015))).fv) 0)

noncomputable def nb054_alpha_dummy_023 : Var := (freshVar (((Class.cv (nb054_alpha_dummy_015))).fv) 1)

noncomputable def nb054_alpha_dummy_024 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb054_alpha_dummy_017 x y))).fv) 0)

noncomputable def nb054_alpha_dummy_025 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb054_alpha_dummy_017 x y))).fv) 1)

noncomputable def nb054_alpha_dummy_026 : Var := (freshVar (((Wff.classMem (Class.cv (nb054_alpha_dummy_022)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb054_alpha_dummy_022)) (syn_c1c))).fv ∪ ((Class.cv (nb054_alpha_dummy_022))).fv) 0)

noncomputable def nb054_alpha_dummy_027 (x : Var) (y : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb054_alpha_dummy_024 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb054_alpha_dummy_024 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb054_alpha_dummy_024 x y))).fv) 0)

noncomputable def nb054_alpha_dummy_028 : Var := (freshVar (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb054_alpha_dummy_029 : Var := (freshVar (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb054_alpha_dummy_030 : Var := (freshVar (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb054_alpha_dummy_031 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb054_alpha_dummy_032 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb054_alpha_dummy_033 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb054_alpha_dummy_034 : Var := (freshVar (((syn_cnin (Class.cv (nb054_alpha_dummy_029)) (Class.cv (nb054_alpha_dummy_030)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_029)) (Class.cv (nb054_alpha_dummy_030)))).fv) 0)

noncomputable def nb054_alpha_dummy_035 (x : Var) (y : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb054_alpha_dummy_032 x y)) (Class.cv (nb054_alpha_dummy_033 x y)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_032 x y)) (Class.cv (nb054_alpha_dummy_033 x y)))).fv) 0)

noncomputable def nb054_alpha_dummy_036 : Var := (freshVar (((Class.cv (nb054_alpha_dummy_029))).fv ∪ ((Class.cv (nb054_alpha_dummy_030))).fv) 0)

noncomputable def nb054_alpha_dummy_037 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb054_alpha_dummy_032 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_033 x y))).fv) 0)

noncomputable def nb054_alpha_dummy_038 : Var := (freshVar (((syn_ccompl (Class.cv (nb054_alpha_dummy_029)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_030)))).fv) 0)

noncomputable def nb054_alpha_dummy_039 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb054_alpha_dummy_032 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_033 x y)))).fv) 0)

noncomputable def nb054_alpha_dummy_040 : Var := (freshVar (((Class.cv (nb054_alpha_dummy_029))).fv ∪ ((Class.cv (nb054_alpha_dummy_029))).fv) 0)

noncomputable def nb054_alpha_dummy_041 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb054_alpha_dummy_032 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_032 x y))).fv) 0)

noncomputable def nb054_alpha_dummy_042 : Var := (freshVar (((Class.cv (nb054_alpha_dummy_030))).fv ∪ ((Class.cv (nb054_alpha_dummy_030))).fv) 0)

noncomputable def nb054_alpha_dummy_043 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb054_alpha_dummy_033 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_033 x y))).fv) 0)

noncomputable def nb054_alpha_dummy_044 : Var := (freshVar (((Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_001)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_015))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_001)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_015))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb054_alpha_dummy_045 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb054_alpha_dummy_046 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb054_alpha_dummy_015))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb054_alpha_dummy_047 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb054_alpha_dummy_048 : Var := (freshVar (((syn_cphi (Class.cv (nb054_alpha_dummy_015)))).fv ∪ ((syn_cphi (Class.cv (nb054_alpha_dummy_015)))).fv) 0)

noncomputable def nb054_alpha_dummy_049 (x : Var) (y : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb054_alpha_dummy_017 x y)))).fv ∪ ((syn_cphi (Class.cv (nb054_alpha_dummy_017 x y)))).fv) 0)

noncomputable def nb054_alpha_dummy_050 : Var := (freshVar (((Class.cv (nb054_alpha_dummy_007))).fv) 0)

noncomputable def nb054_alpha_dummy_051 : Var := (freshVar (((Class.cv (nb054_alpha_dummy_007))).fv) 1)

noncomputable def nb054_alpha_dummy_052 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb054_alpha_dummy_009 x y))).fv) 0)

noncomputable def nb054_alpha_dummy_053 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb054_alpha_dummy_009 x y))).fv) 1)

noncomputable def nb054_alpha_dummy_054 : Var := (freshVar (((Wff.classMem (Class.cv (nb054_alpha_dummy_050)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb054_alpha_dummy_050)) (syn_c1c))).fv ∪ ((Class.cv (nb054_alpha_dummy_050))).fv) 0)

noncomputable def nb054_alpha_dummy_055 (x : Var) (y : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb054_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb054_alpha_dummy_052 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb054_alpha_dummy_052 x y))).fv) 0)

noncomputable def nb054_alpha_dummy_056 : Var := (freshVar (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb054_alpha_dummy_057 : Var := (freshVar (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb054_alpha_dummy_058 : Var := (freshVar (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb054_alpha_dummy_059 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb054_alpha_dummy_060 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb054_alpha_dummy_061 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb054_alpha_dummy_062 : Var := (freshVar (((syn_cnin (Class.cv (nb054_alpha_dummy_057)) (Class.cv (nb054_alpha_dummy_058)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_057)) (Class.cv (nb054_alpha_dummy_058)))).fv) 0)

noncomputable def nb054_alpha_dummy_063 (x : Var) (y : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb054_alpha_dummy_060 x y)) (Class.cv (nb054_alpha_dummy_061 x y)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_060 x y)) (Class.cv (nb054_alpha_dummy_061 x y)))).fv) 0)

noncomputable def nb054_alpha_dummy_064 : Var := (freshVar (((Class.cv (nb054_alpha_dummy_057))).fv ∪ ((Class.cv (nb054_alpha_dummy_058))).fv) 0)

noncomputable def nb054_alpha_dummy_065 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb054_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_061 x y))).fv) 0)

noncomputable def nb054_alpha_dummy_066 : Var := (freshVar (((syn_ccompl (Class.cv (nb054_alpha_dummy_057)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_058)))).fv) 0)

noncomputable def nb054_alpha_dummy_067 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb054_alpha_dummy_060 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_061 x y)))).fv) 0)

noncomputable def nb054_alpha_dummy_068 : Var := (freshVar (((Class.cv (nb054_alpha_dummy_057))).fv ∪ ((Class.cv (nb054_alpha_dummy_057))).fv) 0)

noncomputable def nb054_alpha_dummy_069 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb054_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_060 x y))).fv) 0)

noncomputable def nb054_alpha_dummy_070 : Var := (freshVar (((Class.cv (nb054_alpha_dummy_058))).fv ∪ ((Class.cv (nb054_alpha_dummy_058))).fv) 0)

noncomputable def nb054_alpha_dummy_071 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb054_alpha_dummy_061 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_061 x y))).fv) 0)

noncomputable def nb054_alpha_dummy_072 : Var := (freshVar (((Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (Class.cv (nb054_alpha_dummy_002)) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_007))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (Class.cv (nb054_alpha_dummy_002)) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_007))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb054_alpha_dummy_073 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (Class.cv (nb054_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (Class.cv (nb054_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb054_alpha_dummy_074 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb054_alpha_dummy_007))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb054_alpha_dummy_075 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb054_alpha_dummy_076 : Var := (freshVar (((syn_cphi (Class.cv (nb054_alpha_dummy_007)))).fv ∪ ((syn_cphi (Class.cv (nb054_alpha_dummy_007)))).fv) 0)

noncomputable def nb054_alpha_dummy_077 (x : Var) (y : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb054_alpha_dummy_009 x y)))).fv ∪ ((syn_cphi (Class.cv (nb054_alpha_dummy_009 x y)))).fv) 0)

noncomputable def nb054_alpha_dummy_078 : Var := (freshVar (((Class.cv (nb054_alpha_dummy_000))).fv ∪ ((Class.cv (nb054_alpha_dummy_001))).fv) 2)

noncomputable def nb054_alpha_dummy_079 (x : Var) (y : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 2)

noncomputable def nb054_alpha_dummy_080 : Var := (freshVar (((syn_cnin (Class.cv (nb054_alpha_dummy_015)) (Class.cv (nb054_alpha_dummy_078)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_015)) (Class.cv (nb054_alpha_dummy_078)))).fv) 0)

noncomputable def nb054_alpha_dummy_081 (x : Var) (y : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb054_alpha_dummy_017 x y)) (Class.cv (nb054_alpha_dummy_079 x y)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_017 x y)) (Class.cv (nb054_alpha_dummy_079 x y)))).fv) 0)

noncomputable def nb054_alpha_dummy_082 : Var := (freshVar (((Class.cv (nb054_alpha_dummy_015))).fv ∪ ((Class.cv (nb054_alpha_dummy_078))).fv) 0)

noncomputable def nb054_alpha_dummy_083 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb054_alpha_dummy_017 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_079 x y))).fv) 0)

noncomputable def nb054_alpha_dummy_084 : Var := (freshVar (((syn_ccompl (Class.cv (nb054_alpha_dummy_015)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_078)))).fv) 0)

noncomputable def nb054_alpha_dummy_085 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb054_alpha_dummy_017 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_079 x y)))).fv) 0)

noncomputable def nb054_alpha_dummy_086 : Var := (freshVar (((Class.cv (nb054_alpha_dummy_015))).fv ∪ ((Class.cv (nb054_alpha_dummy_015))).fv) 0)

noncomputable def nb054_alpha_dummy_087 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb054_alpha_dummy_017 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_017 x y))).fv) 0)

noncomputable def nb054_alpha_dummy_088 : Var := (freshVar (((Class.cv (nb054_alpha_dummy_078))).fv ∪ ((Class.cv (nb054_alpha_dummy_078))).fv) 0)

noncomputable def nb054_alpha_dummy_089 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb054_alpha_dummy_079 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_079 x y))).fv) 0)

theorem nb054_fresh_000 : (nb054_alpha_dummy_072) ∉ (((Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (Class.cv (nb054_alpha_dummy_002)) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_007))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (Class.cv (nb054_alpha_dummy_002)) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_007))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb054_alpha_dummy_072] using freshVar_not_mem (((Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (Class.cv (nb054_alpha_dummy_002)) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_007))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (Class.cv (nb054_alpha_dummy_002)) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_007))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb054_fresh_001 : (nb054_alpha_dummy_012) ∉ (((Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001))) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cphi (Class.cv (nb054_alpha_dummy_007))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001))) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cphi (Class.cv (nb054_alpha_dummy_007))))))).fv) := by
  simpa only [nb054_alpha_dummy_012] using freshVar_not_mem (((Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001))) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cphi (Class.cv (nb054_alpha_dummy_007))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001))) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cphi (Class.cv (nb054_alpha_dummy_007))))))).fv) 0

theorem nb054_fresh_002 (x : Var) (y : Var) : (nb054_alpha_dummy_073 x y) ∉ (((Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (Class.cv (nb054_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (Class.cv (nb054_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb054_alpha_dummy_073] using freshVar_not_mem (((Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (Class.cv (nb054_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (Class.cv (nb054_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb054_fresh_003 (x : Var) (y : Var) : (nb054_alpha_dummy_013 x y) ∉ (((Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))))))).fv) := by
  simpa only [nb054_alpha_dummy_013] using freshVar_not_mem (((Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))))))).fv) 0

theorem nb054_fresh_004 : (nb054_alpha_dummy_020) ∉ (((Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_000)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cphi (Class.cv (nb054_alpha_dummy_015))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_000)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cphi (Class.cv (nb054_alpha_dummy_015))))))).fv) := by
  simpa only [nb054_alpha_dummy_020] using freshVar_not_mem (((Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_000)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cphi (Class.cv (nb054_alpha_dummy_015))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_000)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cphi (Class.cv (nb054_alpha_dummy_015))))))).fv) 0

theorem nb054_fresh_005 : (nb054_alpha_dummy_044) ∉ (((Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_001)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_015))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_001)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_015))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb054_alpha_dummy_044] using freshVar_not_mem (((Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_001)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_015))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_001)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_015))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb054_fresh_006 (x : Var) (y : Var) : (nb054_alpha_dummy_021 x y) ∉ (((Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))))))).fv) := by
  simpa only [nb054_alpha_dummy_021] using freshVar_not_mem (((Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))))))).fv) 0

theorem nb054_fresh_007 (x : Var) (y : Var) : (nb054_alpha_dummy_045 x y) ∉ (((Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb054_alpha_dummy_045] using freshVar_not_mem (((Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb054_fresh_008 : (nb054_alpha_dummy_014) ∉ (((Class.cv (nb054_alpha_dummy_000))).fv ∪ ((Class.cv (nb054_alpha_dummy_001))).fv) := by
  simpa only [nb054_alpha_dummy_014] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_000))).fv ∪ ((Class.cv (nb054_alpha_dummy_001))).fv) 0

theorem nb054_fresh_009 : (nb054_alpha_dummy_015) ∉ (((Class.cv (nb054_alpha_dummy_000))).fv ∪ ((Class.cv (nb054_alpha_dummy_001))).fv) := by
  simpa only [nb054_alpha_dummy_015] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_000))).fv ∪ ((Class.cv (nb054_alpha_dummy_001))).fv) 1

theorem nb054_fresh_010 : (nb054_alpha_dummy_078) ∉ (((Class.cv (nb054_alpha_dummy_000))).fv ∪ ((Class.cv (nb054_alpha_dummy_001))).fv) := by
  simpa only [nb054_alpha_dummy_078] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_000))).fv ∪ ((Class.cv (nb054_alpha_dummy_001))).fv) 2

theorem nb054_distinct_011 : (nb054_alpha_dummy_014) ≠ (nb054_alpha_dummy_015) := by
  simpa only [nb054_alpha_dummy_014, nb054_alpha_dummy_015] using
    (freshVar_injective (((Class.cv (nb054_alpha_dummy_000))).fv ∪ ((Class.cv (nb054_alpha_dummy_001))).fv) (i := 0) (j := 1) (by decide))

theorem nb054_distinct_012 : (nb054_alpha_dummy_014) ≠ (nb054_alpha_dummy_078) := by
  simpa only [nb054_alpha_dummy_014, nb054_alpha_dummy_078] using
    (freshVar_injective (((Class.cv (nb054_alpha_dummy_000))).fv ∪ ((Class.cv (nb054_alpha_dummy_001))).fv) (i := 0) (j := 2) (by decide))

theorem nb054_distinct_013 : (nb054_alpha_dummy_015) ≠ (nb054_alpha_dummy_078) := by
  simpa only [nb054_alpha_dummy_015, nb054_alpha_dummy_078] using
    (freshVar_injective (((Class.cv (nb054_alpha_dummy_000))).fv ∪ ((Class.cv (nb054_alpha_dummy_001))).fv) (i := 1) (j := 2) (by decide))

theorem nb054_fresh_014 : (nb054_alpha_dummy_050) ∉ (((Class.cv (nb054_alpha_dummy_007))).fv) := by
  simpa only [nb054_alpha_dummy_050] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_007))).fv) 0

theorem nb054_fresh_015 : (nb054_alpha_dummy_051) ∉ (((Class.cv (nb054_alpha_dummy_007))).fv) := by
  simpa only [nb054_alpha_dummy_051] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_007))).fv) 1

theorem nb054_distinct_016 : (nb054_alpha_dummy_050) ≠ (nb054_alpha_dummy_051) := by
  simpa only [nb054_alpha_dummy_050, nb054_alpha_dummy_051] using
    (freshVar_injective (((Class.cv (nb054_alpha_dummy_007))).fv) (i := 0) (j := 1) (by decide))

theorem nb054_fresh_017 (x : Var) (y : Var) : (nb054_alpha_dummy_052 x y) ∉ (((Class.cv (nb054_alpha_dummy_009 x y))).fv) := by
  simpa only [nb054_alpha_dummy_052] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_009 x y))).fv) 0

theorem nb054_fresh_018 (x : Var) (y : Var) : (nb054_alpha_dummy_053 x y) ∉ (((Class.cv (nb054_alpha_dummy_009 x y))).fv) := by
  simpa only [nb054_alpha_dummy_053] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_009 x y))).fv) 1

theorem nb054_distinct_019 (x : Var) (y : Var) : (nb054_alpha_dummy_052 x y) ≠ (nb054_alpha_dummy_053 x y) := by
  simpa only [nb054_alpha_dummy_052, nb054_alpha_dummy_053] using
    (freshVar_injective (((Class.cv (nb054_alpha_dummy_009 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb054_fresh_020 : (nb054_alpha_dummy_022) ∉ (((Class.cv (nb054_alpha_dummy_015))).fv) := by
  simpa only [nb054_alpha_dummy_022] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_015))).fv) 0

theorem nb054_fresh_021 : (nb054_alpha_dummy_023) ∉ (((Class.cv (nb054_alpha_dummy_015))).fv) := by
  simpa only [nb054_alpha_dummy_023] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_015))).fv) 1

theorem nb054_distinct_022 : (nb054_alpha_dummy_022) ≠ (nb054_alpha_dummy_023) := by
  simpa only [nb054_alpha_dummy_022, nb054_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb054_alpha_dummy_015))).fv) (i := 0) (j := 1) (by decide))

theorem nb054_fresh_023 : (nb054_alpha_dummy_086) ∉ (((Class.cv (nb054_alpha_dummy_015))).fv ∪ ((Class.cv (nb054_alpha_dummy_015))).fv) := by
  simpa only [nb054_alpha_dummy_086] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_015))).fv ∪ ((Class.cv (nb054_alpha_dummy_015))).fv) 0

theorem nb054_fresh_024 : (nb054_alpha_dummy_082) ∉ (((Class.cv (nb054_alpha_dummy_015))).fv ∪ ((Class.cv (nb054_alpha_dummy_078))).fv) := by
  simpa only [nb054_alpha_dummy_082] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_015))).fv ∪ ((Class.cv (nb054_alpha_dummy_078))).fv) 0

theorem nb054_fresh_025 (x : Var) (y : Var) : (nb054_alpha_dummy_024 x y) ∉ (((Class.cv (nb054_alpha_dummy_017 x y))).fv) := by
  simpa only [nb054_alpha_dummy_024] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_017 x y))).fv) 0

theorem nb054_fresh_026 (x : Var) (y : Var) : (nb054_alpha_dummy_025 x y) ∉ (((Class.cv (nb054_alpha_dummy_017 x y))).fv) := by
  simpa only [nb054_alpha_dummy_025] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_017 x y))).fv) 1

theorem nb054_distinct_027 (x : Var) (y : Var) : (nb054_alpha_dummy_024 x y) ≠ (nb054_alpha_dummy_025 x y) := by
  simpa only [nb054_alpha_dummy_024, nb054_alpha_dummy_025] using
    (freshVar_injective (((Class.cv (nb054_alpha_dummy_017 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb054_fresh_028 (x : Var) (y : Var) : (nb054_alpha_dummy_087 x y) ∉ (((Class.cv (nb054_alpha_dummy_017 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_017 x y))).fv) := by
  simpa only [nb054_alpha_dummy_087] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_017 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_017 x y))).fv) 0

theorem nb054_fresh_029 (x : Var) (y : Var) : (nb054_alpha_dummy_083 x y) ∉ (((Class.cv (nb054_alpha_dummy_017 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_079 x y))).fv) := by
  simpa only [nb054_alpha_dummy_083] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_017 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_079 x y))).fv) 0

theorem nb054_fresh_030 : (nb054_alpha_dummy_028) ∉ (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb054_alpha_dummy_028] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 0

theorem nb054_fresh_031 : (nb054_alpha_dummy_029) ∉ (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb054_alpha_dummy_029] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 1

theorem nb054_fresh_032 : (nb054_alpha_dummy_030) ∉ (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb054_alpha_dummy_030] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) 2

theorem nb054_distinct_033 : (nb054_alpha_dummy_028) ≠ (nb054_alpha_dummy_029) := by
  simpa only [nb054_alpha_dummy_028, nb054_alpha_dummy_029] using
    (freshVar_injective (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb054_distinct_034 : (nb054_alpha_dummy_028) ≠ (nb054_alpha_dummy_030) := by
  simpa only [nb054_alpha_dummy_028, nb054_alpha_dummy_030] using
    (freshVar_injective (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb054_distinct_035 : (nb054_alpha_dummy_029) ≠ (nb054_alpha_dummy_030) := by
  simpa only [nb054_alpha_dummy_029, nb054_alpha_dummy_030] using
    (freshVar_injective (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb054_fresh_036 (x : Var) (y : Var) : (nb054_alpha_dummy_031 x y) ∉ (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb054_alpha_dummy_031] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb054_fresh_037 (x : Var) (y : Var) : (nb054_alpha_dummy_032 x y) ∉ (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb054_alpha_dummy_032] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb054_fresh_038 (x : Var) (y : Var) : (nb054_alpha_dummy_033 x y) ∉ (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb054_alpha_dummy_033] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb054_distinct_039 (x : Var) (y : Var) : (nb054_alpha_dummy_031 x y) ≠ (nb054_alpha_dummy_032 x y) := by
  simpa only [nb054_alpha_dummy_031, nb054_alpha_dummy_032] using
    (freshVar_injective (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb054_distinct_040 (x : Var) (y : Var) : (nb054_alpha_dummy_031 x y) ≠ (nb054_alpha_dummy_033 x y) := by
  simpa only [nb054_alpha_dummy_031, nb054_alpha_dummy_033] using
    (freshVar_injective (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb054_distinct_041 (x : Var) (y : Var) : (nb054_alpha_dummy_032 x y) ≠ (nb054_alpha_dummy_033 x y) := by
  simpa only [nb054_alpha_dummy_032, nb054_alpha_dummy_033] using
    (freshVar_injective (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb054_fresh_042 : (nb054_alpha_dummy_040) ∉ (((Class.cv (nb054_alpha_dummy_029))).fv ∪ ((Class.cv (nb054_alpha_dummy_029))).fv) := by
  simpa only [nb054_alpha_dummy_040] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_029))).fv ∪ ((Class.cv (nb054_alpha_dummy_029))).fv) 0

theorem nb054_fresh_043 : (nb054_alpha_dummy_036) ∉ (((Class.cv (nb054_alpha_dummy_029))).fv ∪ ((Class.cv (nb054_alpha_dummy_030))).fv) := by
  simpa only [nb054_alpha_dummy_036] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_029))).fv ∪ ((Class.cv (nb054_alpha_dummy_030))).fv) 0

theorem nb054_fresh_044 : (nb054_alpha_dummy_042) ∉ (((Class.cv (nb054_alpha_dummy_030))).fv ∪ ((Class.cv (nb054_alpha_dummy_030))).fv) := by
  simpa only [nb054_alpha_dummy_042] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_030))).fv ∪ ((Class.cv (nb054_alpha_dummy_030))).fv) 0

theorem nb054_fresh_045 (x : Var) (y : Var) : (nb054_alpha_dummy_041 x y) ∉ (((Class.cv (nb054_alpha_dummy_032 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_032 x y))).fv) := by
  simpa only [nb054_alpha_dummy_041] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_032 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_032 x y))).fv) 0

theorem nb054_fresh_046 (x : Var) (y : Var) : (nb054_alpha_dummy_037 x y) ∉ (((Class.cv (nb054_alpha_dummy_032 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_033 x y))).fv) := by
  simpa only [nb054_alpha_dummy_037] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_032 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_033 x y))).fv) 0

theorem nb054_fresh_047 (x : Var) (y : Var) : (nb054_alpha_dummy_043 x y) ∉ (((Class.cv (nb054_alpha_dummy_033 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_033 x y))).fv) := by
  simpa only [nb054_alpha_dummy_043] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_033 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_033 x y))).fv) 0

theorem nb054_fresh_048 : (nb054_alpha_dummy_056) ∉ (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb054_alpha_dummy_056] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 0

theorem nb054_fresh_049 : (nb054_alpha_dummy_057) ∉ (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb054_alpha_dummy_057] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 1

theorem nb054_fresh_050 : (nb054_alpha_dummy_058) ∉ (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb054_alpha_dummy_058] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 2

theorem nb054_distinct_051 : (nb054_alpha_dummy_056) ≠ (nb054_alpha_dummy_057) := by
  simpa only [nb054_alpha_dummy_056, nb054_alpha_dummy_057] using
    (freshVar_injective (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb054_distinct_052 : (nb054_alpha_dummy_056) ≠ (nb054_alpha_dummy_058) := by
  simpa only [nb054_alpha_dummy_056, nb054_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb054_distinct_053 : (nb054_alpha_dummy_057) ≠ (nb054_alpha_dummy_058) := by
  simpa only [nb054_alpha_dummy_057, nb054_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb054_fresh_054 (x : Var) (y : Var) : (nb054_alpha_dummy_059 x y) ∉ (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb054_alpha_dummy_059] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb054_fresh_055 (x : Var) (y : Var) : (nb054_alpha_dummy_060 x y) ∉ (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb054_alpha_dummy_060] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb054_fresh_056 (x : Var) (y : Var) : (nb054_alpha_dummy_061 x y) ∉ (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb054_alpha_dummy_061] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb054_distinct_057 (x : Var) (y : Var) : (nb054_alpha_dummy_059 x y) ≠ (nb054_alpha_dummy_060 x y) := by
  simpa only [nb054_alpha_dummy_059, nb054_alpha_dummy_060] using
    (freshVar_injective (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb054_distinct_058 (x : Var) (y : Var) : (nb054_alpha_dummy_059 x y) ≠ (nb054_alpha_dummy_061 x y) := by
  simpa only [nb054_alpha_dummy_059, nb054_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb054_distinct_059 (x : Var) (y : Var) : (nb054_alpha_dummy_060 x y) ≠ (nb054_alpha_dummy_061 x y) := by
  simpa only [nb054_alpha_dummy_060, nb054_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
