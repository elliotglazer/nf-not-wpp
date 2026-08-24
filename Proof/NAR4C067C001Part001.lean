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

noncomputable def nb067_alpha_dummy_000 : Var := (freshVar ((∅ : Finset Var)) 0)

noncomputable def nb067_alpha_dummy_001 : Var := (freshVar ((∅ : Finset Var)) 1)

noncomputable def nb067_alpha_dummy_002 : Var := (freshVar ((∅ : Finset Var)) 2)

noncomputable def nb067_alpha_dummy_003 : Var := (freshVar (({(nb067_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({(nb067_alpha_dummy_002)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((Class.cab (nb067_alpha_dummy_000) (syn_wf (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_002)) (Class.cv (nb067_alpha_dummy_001))))).fv) 0)

noncomputable def nb067_alpha_dummy_004 (x : Var) (y : Var) (f : Var) : Var := (freshVar (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({y} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((Class.cab f (syn_wf (Class.cv f) (Class.cv y) (Class.cv x)))).fv) 0)

noncomputable def nb067_alpha_dummy_005 : Var := (freshVar (({(nb067_alpha_dummy_001)} : Finset Var) ∪ ({(nb067_alpha_dummy_002)} : Finset Var) ∪ ({(nb067_alpha_dummy_003)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_001)) (syn_cvv)) (Wff.classMem (Class.cv (nb067_alpha_dummy_002)) (syn_cvv))) (Wff.classEq (Class.cv (nb067_alpha_dummy_003)) (Class.cab (nb067_alpha_dummy_000) (syn_wf (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_002)) (Class.cv (nb067_alpha_dummy_001))))))).fv) 0)

noncomputable def nb067_alpha_dummy_006 (x : Var) (y : Var) (f : Var) : Var := (freshVar (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb067_alpha_dummy_004 x y f)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv))) (Wff.classEq (Class.cv (nb067_alpha_dummy_004 x y f)) (Class.cab f (syn_wf (Class.cv f) (Class.cv y) (Class.cv x)))))).fv) 0)

noncomputable def nb067_alpha_dummy_007 : Var := (freshVar (((syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))).fv ∪ ((Class.cv (nb067_alpha_dummy_003))).fv) 0)

noncomputable def nb067_alpha_dummy_008 : Var := (freshVar (((syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))).fv ∪ ((Class.cv (nb067_alpha_dummy_003))).fv) 1)

noncomputable def nb067_alpha_dummy_009 (x : Var) (y : Var) (f : Var) : Var := (freshVar (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb067_alpha_dummy_004 x y f))).fv) 0)

noncomputable def nb067_alpha_dummy_010 (x : Var) (y : Var) (f : Var) : Var := (freshVar (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb067_alpha_dummy_004 x y f))).fv) 1)

noncomputable def nb067_alpha_dummy_011 : Var := (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002))) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cphi (Class.cv (nb067_alpha_dummy_008)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003)) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb067_alpha_dummy_012 (x : Var) (y : Var) (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (Class.cv (nb067_alpha_dummy_004 x y f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb067_alpha_dummy_013 : Var := (freshVar (((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002))) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cphi (Class.cv (nb067_alpha_dummy_008))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002))) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cphi (Class.cv (nb067_alpha_dummy_008))))))).fv) 0)

noncomputable def nb067_alpha_dummy_014 (x : Var) (y : Var) (f : Var) : Var := (freshVar (((Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))))).fv) 0)

noncomputable def nb067_alpha_dummy_015 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_001))).fv ∪ ((Class.cv (nb067_alpha_dummy_002))).fv) 0)

noncomputable def nb067_alpha_dummy_016 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_001))).fv ∪ ((Class.cv (nb067_alpha_dummy_002))).fv) 1)

noncomputable def nb067_alpha_dummy_017 (x : Var) (y : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

noncomputable def nb067_alpha_dummy_018 (x : Var) (y : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

noncomputable def nb067_alpha_dummy_019 : Var := (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cphi (Class.cv (nb067_alpha_dummy_016)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb067_alpha_dummy_020 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb067_alpha_dummy_021 : Var := (freshVar (((Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cphi (Class.cv (nb067_alpha_dummy_016))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cphi (Class.cv (nb067_alpha_dummy_016))))))).fv) 0)

noncomputable def nb067_alpha_dummy_022 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))))))).fv) 0)

noncomputable def nb067_alpha_dummy_023 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_016))).fv) 0)

noncomputable def nb067_alpha_dummy_024 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_016))).fv) 1)

noncomputable def nb067_alpha_dummy_025 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_018 x y))).fv) 0)

noncomputable def nb067_alpha_dummy_026 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_018 x y))).fv) 1)

noncomputable def nb067_alpha_dummy_027 : Var := (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_023)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_023)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_023))).fv) 0)

noncomputable def nb067_alpha_dummy_028 (x : Var) (y : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_025 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_025 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_025 x y))).fv) 0)

noncomputable def nb067_alpha_dummy_029 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb067_alpha_dummy_030 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb067_alpha_dummy_031 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb067_alpha_dummy_032 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb067_alpha_dummy_033 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb067_alpha_dummy_034 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb067_alpha_dummy_035 : Var := (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_030)) (Class.cv (nb067_alpha_dummy_031)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_030)) (Class.cv (nb067_alpha_dummy_031)))).fv) 0)

noncomputable def nb067_alpha_dummy_036 (x : Var) (y : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_033 x y)) (Class.cv (nb067_alpha_dummy_034 x y)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_033 x y)) (Class.cv (nb067_alpha_dummy_034 x y)))).fv) 0)

noncomputable def nb067_alpha_dummy_037 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_030))).fv ∪ ((Class.cv (nb067_alpha_dummy_031))).fv) 0)

noncomputable def nb067_alpha_dummy_038 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_033 x y))).fv ∪ ((Class.cv (nb067_alpha_dummy_034 x y))).fv) 0)

noncomputable def nb067_alpha_dummy_039 : Var := (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_030)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_031)))).fv) 0)

noncomputable def nb067_alpha_dummy_040 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_033 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_034 x y)))).fv) 0)

noncomputable def nb067_alpha_dummy_041 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_030))).fv ∪ ((Class.cv (nb067_alpha_dummy_030))).fv) 0)

noncomputable def nb067_alpha_dummy_042 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_033 x y))).fv ∪ ((Class.cv (nb067_alpha_dummy_033 x y))).fv) 0)

noncomputable def nb067_alpha_dummy_043 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_031))).fv ∪ ((Class.cv (nb067_alpha_dummy_031))).fv) 0)

noncomputable def nb067_alpha_dummy_044 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_034 x y))).fv ∪ ((Class.cv (nb067_alpha_dummy_034 x y))).fv) 0)

noncomputable def nb067_alpha_dummy_045 : Var := (freshVar (((Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb067_alpha_dummy_046 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb067_alpha_dummy_047 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_016))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb067_alpha_dummy_048 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb067_alpha_dummy_049 : Var := (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_016)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_016)))).fv) 0)

noncomputable def nb067_alpha_dummy_050 (x : Var) (y : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))).fv) 0)

noncomputable def nb067_alpha_dummy_051 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_008))).fv) 0)

noncomputable def nb067_alpha_dummy_052 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_008))).fv) 1)

noncomputable def nb067_alpha_dummy_053 (x : Var) (y : Var) (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_010 x y f))).fv) 0)

noncomputable def nb067_alpha_dummy_054 (x : Var) (y : Var) (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_010 x y f))).fv) 1)

noncomputable def nb067_alpha_dummy_055 : Var := (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_051)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_051)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_051))).fv) 0)

noncomputable def nb067_alpha_dummy_056 (x : Var) (y : Var) (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_053 x y f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_053 x y f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_053 x y f))).fv) 0)

noncomputable def nb067_alpha_dummy_057 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb067_alpha_dummy_058 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb067_alpha_dummy_059 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb067_alpha_dummy_060 (x : Var) (y : Var) (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb067_alpha_dummy_061 (x : Var) (y : Var) (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb067_alpha_dummy_062 (x : Var) (y : Var) (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb067_alpha_dummy_063 : Var := (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_058)) (Class.cv (nb067_alpha_dummy_059)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_058)) (Class.cv (nb067_alpha_dummy_059)))).fv) 0)

noncomputable def nb067_alpha_dummy_064 (x : Var) (y : Var) (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_061 x y f)) (Class.cv (nb067_alpha_dummy_062 x y f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_061 x y f)) (Class.cv (nb067_alpha_dummy_062 x y f)))).fv) 0)

noncomputable def nb067_alpha_dummy_065 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_058))).fv ∪ ((Class.cv (nb067_alpha_dummy_059))).fv) 0)

noncomputable def nb067_alpha_dummy_066 (x : Var) (y : Var) (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_061 x y f))).fv ∪ ((Class.cv (nb067_alpha_dummy_062 x y f))).fv) 0)

noncomputable def nb067_alpha_dummy_067 : Var := (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_058)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_059)))).fv) 0)

noncomputable def nb067_alpha_dummy_068 (x : Var) (y : Var) (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_061 x y f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_062 x y f)))).fv) 0)

noncomputable def nb067_alpha_dummy_069 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_058))).fv ∪ ((Class.cv (nb067_alpha_dummy_058))).fv) 0)

noncomputable def nb067_alpha_dummy_070 (x : Var) (y : Var) (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_061 x y f))).fv ∪ ((Class.cv (nb067_alpha_dummy_061 x y f))).fv) 0)

noncomputable def nb067_alpha_dummy_071 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_059))).fv ∪ ((Class.cv (nb067_alpha_dummy_059))).fv) 0)

noncomputable def nb067_alpha_dummy_072 (x : Var) (y : Var) (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_062 x y f))).fv ∪ ((Class.cv (nb067_alpha_dummy_062 x y f))).fv) 0)

noncomputable def nb067_alpha_dummy_073 : Var := (freshVar (((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003)) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003)) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb067_alpha_dummy_074 (x : Var) (y : Var) (f : Var) : Var := (freshVar (((Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (Class.cv (nb067_alpha_dummy_004 x y f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (Class.cv (nb067_alpha_dummy_004 x y f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb067_alpha_dummy_075 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_008))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb067_alpha_dummy_076 (x : Var) (y : Var) (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb067_alpha_dummy_077 : Var := (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_008)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_008)))).fv) 0)

noncomputable def nb067_alpha_dummy_078 (x : Var) (y : Var) (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))).fv) 0)

noncomputable def nb067_alpha_dummy_079 : Var := (freshVar (((syn_cnin (syn_ccom (Class.cv (nb067_alpha_dummy_000)) (syn_ccnv (Class.cv (nb067_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb067_alpha_dummy_000)) (syn_ccnv (Class.cv (nb067_alpha_dummy_000)))) (syn_cid))).fv) 0)

noncomputable def nb067_alpha_dummy_080 (f : Var) : Var := (freshVar (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) 0)

noncomputable def nb067_alpha_dummy_081 : Var := (freshVar (((syn_ccom (Class.cv (nb067_alpha_dummy_000)) (syn_ccnv (Class.cv (nb067_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) 0)

noncomputable def nb067_alpha_dummy_082 (f : Var) : Var := (freshVar (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) 0)

noncomputable def nb067_alpha_dummy_083 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) 0)

noncomputable def nb067_alpha_dummy_084 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) 1)

noncomputable def nb067_alpha_dummy_085 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) 2)

noncomputable def nb067_alpha_dummy_086 (f : Var) : Var := (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 0)

noncomputable def nb067_alpha_dummy_087 (f : Var) : Var := (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 1)

noncomputable def nb067_alpha_dummy_088 (f : Var) : Var := (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 2)

noncomputable def nb067_alpha_dummy_089 : Var := (freshVar (({(nb067_alpha_dummy_083)} : Finset Var) ∪ ({(nb067_alpha_dummy_084)} : Finset Var) ∪ ((syn_wex (nb067_alpha_dummy_085) (syn_wa (syn_wbr (Class.cv (nb067_alpha_dummy_083)) (syn_ccnv (Class.cv (nb067_alpha_dummy_000))) (Class.cv (nb067_alpha_dummy_085))) (syn_wbr (Class.cv (nb067_alpha_dummy_085)) (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_084)))))).fv) 0)

noncomputable def nb067_alpha_dummy_090 (f : Var) : Var := (freshVar (({(nb067_alpha_dummy_086 f)} : Finset Var) ∪ ({(nb067_alpha_dummy_087 f)} : Finset Var) ∪ ((syn_wex (nb067_alpha_dummy_088 f) (syn_wa (syn_wbr (Class.cv (nb067_alpha_dummy_086 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb067_alpha_dummy_088 f))) (syn_wbr (Class.cv (nb067_alpha_dummy_088 f)) (Class.cv f) (Class.cv (nb067_alpha_dummy_087 f)))))).fv) 0)

noncomputable def nb067_alpha_dummy_091 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) 0)

noncomputable def nb067_alpha_dummy_092 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) 1)

noncomputable def nb067_alpha_dummy_093 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) 0)

noncomputable def nb067_alpha_dummy_094 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) 1)

noncomputable def nb067_alpha_dummy_095 : Var := (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cphi (Class.cv (nb067_alpha_dummy_092)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb067_alpha_dummy_096 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb067_alpha_dummy_097 : Var := (freshVar (((Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cphi (Class.cv (nb067_alpha_dummy_092))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cphi (Class.cv (nb067_alpha_dummy_092))))))).fv) 0)

noncomputable def nb067_alpha_dummy_098 (f : Var) : Var := (freshVar (((Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))))))).fv) 0)

noncomputable def nb067_alpha_dummy_099 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_092))).fv) 0)

noncomputable def nb067_alpha_dummy_100 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_092))).fv) 1)

noncomputable def nb067_alpha_dummy_101 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_094 f))).fv) 0)

noncomputable def nb067_alpha_dummy_102 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_094 f))).fv) 1)

noncomputable def nb067_alpha_dummy_103 : Var := (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_099)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_099)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_099))).fv) 0)

noncomputable def nb067_alpha_dummy_104 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_101 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_101 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_101 f))).fv) 0)

noncomputable def nb067_alpha_dummy_105 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb067_alpha_dummy_106 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb067_alpha_dummy_107 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb067_alpha_dummy_108 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb067_alpha_dummy_109 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb067_alpha_dummy_110 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb067_alpha_dummy_111 : Var := (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_106)) (Class.cv (nb067_alpha_dummy_107)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_106)) (Class.cv (nb067_alpha_dummy_107)))).fv) 0)

noncomputable def nb067_alpha_dummy_112 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_109 f)) (Class.cv (nb067_alpha_dummy_110 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_109 f)) (Class.cv (nb067_alpha_dummy_110 f)))).fv) 0)

noncomputable def nb067_alpha_dummy_113 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_106))).fv ∪ ((Class.cv (nb067_alpha_dummy_107))).fv) 0)

noncomputable def nb067_alpha_dummy_114 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_110 f))).fv) 0)

noncomputable def nb067_alpha_dummy_115 : Var := (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_106)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_107)))).fv) 0)

noncomputable def nb067_alpha_dummy_116 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_109 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_110 f)))).fv) 0)

noncomputable def nb067_alpha_dummy_117 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_106))).fv ∪ ((Class.cv (nb067_alpha_dummy_106))).fv) 0)

noncomputable def nb067_alpha_dummy_118 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_109 f))).fv) 0)

noncomputable def nb067_alpha_dummy_119 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_107))).fv ∪ ((Class.cv (nb067_alpha_dummy_107))).fv) 0)

noncomputable def nb067_alpha_dummy_120 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_110 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_110 f))).fv) 0)

noncomputable def nb067_alpha_dummy_121 : Var := (freshVar (((Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb067_alpha_dummy_122 (f : Var) : Var := (freshVar (((Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb067_alpha_dummy_123 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_092))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb067_alpha_dummy_124 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb067_alpha_dummy_125 : Var := (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_092)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_092)))).fv) 0)

noncomputable def nb067_alpha_dummy_126 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))).fv) 0)

noncomputable def nb067_alpha_dummy_127 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_085))).fv) 0)

noncomputable def nb067_alpha_dummy_128 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_085))).fv) 1)

noncomputable def nb067_alpha_dummy_129 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_088 f))).fv) 0)

noncomputable def nb067_alpha_dummy_130 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_088 f))).fv) 1)

noncomputable def nb067_alpha_dummy_131 : Var := (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cphi (Class.cv (nb067_alpha_dummy_128)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb067_alpha_dummy_132 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb067_alpha_dummy_133 : Var := (freshVar (((Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cphi (Class.cv (nb067_alpha_dummy_128))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cphi (Class.cv (nb067_alpha_dummy_128))))))).fv) 0)

noncomputable def nb067_alpha_dummy_134 (f : Var) : Var := (freshVar (((Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))))))).fv) 0)

noncomputable def nb067_alpha_dummy_135 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_128))).fv) 0)

noncomputable def nb067_alpha_dummy_136 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_128))).fv) 1)

noncomputable def nb067_alpha_dummy_137 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_130 f))).fv) 0)

noncomputable def nb067_alpha_dummy_138 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_130 f))).fv) 1)

noncomputable def nb067_alpha_dummy_139 : Var := (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_135)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_135)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_135))).fv) 0)

noncomputable def nb067_alpha_dummy_140 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_137 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_137 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_137 f))).fv) 0)

noncomputable def nb067_alpha_dummy_141 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb067_alpha_dummy_142 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb067_alpha_dummy_143 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb067_alpha_dummy_144 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb067_alpha_dummy_145 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb067_alpha_dummy_146 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb067_alpha_dummy_147 : Var := (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143)))).fv) 0)

noncomputable def nb067_alpha_dummy_148 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_145 f)) (Class.cv (nb067_alpha_dummy_146 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_145 f)) (Class.cv (nb067_alpha_dummy_146 f)))).fv) 0)

noncomputable def nb067_alpha_dummy_149 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_142))).fv ∪ ((Class.cv (nb067_alpha_dummy_143))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
