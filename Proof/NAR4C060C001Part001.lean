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

noncomputable def nb060_alpha_dummy_000 : Var := (freshVar ((∅ : Finset Var)) 0)

noncomputable def nb060_alpha_dummy_001 : Var := (freshVar ((∅ : Finset Var)) 1)

noncomputable def nb060_alpha_dummy_002 : Var := (freshVar ((∅ : Finset Var)) 2)

noncomputable def nb060_alpha_dummy_003 : Var := (freshVar ((∅ : Finset Var)) 3)

noncomputable def nb060_alpha_dummy_004 : Var := (freshVar ((∅ : Finset Var)) 4)

noncomputable def nb060_alpha_dummy_005 : Var := (freshVar (({(nb060_alpha_dummy_001)} : Finset Var) ∪ ({(nb060_alpha_dummy_000)} : Finset Var) ∪ ((syn_wral (nb060_alpha_dummy_002) (Class.cv (nb060_alpha_dummy_000)) (syn_wral (nb060_alpha_dummy_003) (Class.cv (nb060_alpha_dummy_000)) (syn_wral (nb060_alpha_dummy_004) (Class.cv (nb060_alpha_dummy_000)) (Wff.imp (syn_wa (syn_wbr (Class.cv (nb060_alpha_dummy_002)) (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_003))) (syn_wbr (Class.cv (nb060_alpha_dummy_003)) (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_004)))) (syn_wbr (Class.cv (nb060_alpha_dummy_002)) (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_004)))))))).fv) 0)

noncomputable def nb060_alpha_dummy_006 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : Var := (freshVar (({r} : Finset Var) ∪ ({a} : Finset Var) ∪ ((syn_wral x (Class.cv a) (syn_wral y (Class.cv a) (syn_wral z (Class.cv a) (Wff.imp (syn_wa (syn_wbr (Class.cv x) (Class.cv r) (Class.cv y)) (syn_wbr (Class.cv y) (Class.cv r) (Class.cv z))) (syn_wbr (Class.cv x) (Class.cv r) (Class.cv z))))))).fv) 0)

noncomputable def nb060_alpha_dummy_007 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_001))).fv ∪ ((Class.cv (nb060_alpha_dummy_000))).fv) 0)

noncomputable def nb060_alpha_dummy_008 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_001))).fv ∪ ((Class.cv (nb060_alpha_dummy_000))).fv) 1)

noncomputable def nb060_alpha_dummy_009 (r : Var) (a : Var) : Var := (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0)

noncomputable def nb060_alpha_dummy_010 (r : Var) (a : Var) : Var := (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1)

noncomputable def nb060_alpha_dummy_011 : Var := (freshVar (((syn_ccompl (Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cphi (Class.cv (nb060_alpha_dummy_008)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb060_alpha_dummy_012 (r : Var) (a : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb060_alpha_dummy_013 : Var := (freshVar (((Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cphi (Class.cv (nb060_alpha_dummy_008))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cphi (Class.cv (nb060_alpha_dummy_008))))))).fv) 0)

noncomputable def nb060_alpha_dummy_014 (r : Var) (a : Var) : Var := (freshVar (((Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))))))).fv) 0)

noncomputable def nb060_alpha_dummy_015 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_008))).fv) 0)

noncomputable def nb060_alpha_dummy_016 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_008))).fv) 1)

noncomputable def nb060_alpha_dummy_017 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_010 r a))).fv) 0)

noncomputable def nb060_alpha_dummy_018 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_010 r a))).fv) 1)

noncomputable def nb060_alpha_dummy_019 : Var := (freshVar (((Wff.classMem (Class.cv (nb060_alpha_dummy_015)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_015)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_015))).fv) 0)

noncomputable def nb060_alpha_dummy_020 (r : Var) (a : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb060_alpha_dummy_017 r a)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_017 r a)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_017 r a))).fv) 0)

noncomputable def nb060_alpha_dummy_021 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb060_alpha_dummy_022 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb060_alpha_dummy_023 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb060_alpha_dummy_024 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb060_alpha_dummy_025 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb060_alpha_dummy_026 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb060_alpha_dummy_027 : Var := (freshVar (((syn_cnin (Class.cv (nb060_alpha_dummy_022)) (Class.cv (nb060_alpha_dummy_023)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_022)) (Class.cv (nb060_alpha_dummy_023)))).fv) 0)

noncomputable def nb060_alpha_dummy_028 (r : Var) (a : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb060_alpha_dummy_025 r a)) (Class.cv (nb060_alpha_dummy_026 r a)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_025 r a)) (Class.cv (nb060_alpha_dummy_026 r a)))).fv) 0)

noncomputable def nb060_alpha_dummy_029 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_022))).fv ∪ ((Class.cv (nb060_alpha_dummy_023))).fv) 0)

noncomputable def nb060_alpha_dummy_030 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_025 r a))).fv ∪ ((Class.cv (nb060_alpha_dummy_026 r a))).fv) 0)

noncomputable def nb060_alpha_dummy_031 : Var := (freshVar (((syn_ccompl (Class.cv (nb060_alpha_dummy_022)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_023)))).fv) 0)

noncomputable def nb060_alpha_dummy_032 (r : Var) (a : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb060_alpha_dummy_025 r a)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_026 r a)))).fv) 0)

noncomputable def nb060_alpha_dummy_033 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_022))).fv ∪ ((Class.cv (nb060_alpha_dummy_022))).fv) 0)

noncomputable def nb060_alpha_dummy_034 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_025 r a))).fv ∪ ((Class.cv (nb060_alpha_dummy_025 r a))).fv) 0)

noncomputable def nb060_alpha_dummy_035 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_023))).fv ∪ ((Class.cv (nb060_alpha_dummy_023))).fv) 0)

noncomputable def nb060_alpha_dummy_036 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_026 r a))).fv ∪ ((Class.cv (nb060_alpha_dummy_026 r a))).fv) 0)

noncomputable def nb060_alpha_dummy_037 : Var := (freshVar (((Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb060_alpha_dummy_038 (r : Var) (a : Var) : Var := (freshVar (((Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb060_alpha_dummy_039 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_008))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb060_alpha_dummy_040 (r : Var) (a : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb060_alpha_dummy_041 : Var := (freshVar (((syn_cphi (Class.cv (nb060_alpha_dummy_008)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_008)))).fv) 0)

noncomputable def nb060_alpha_dummy_042 (r : Var) (a : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))).fv) 0)

noncomputable def nb060_alpha_dummy_043 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_003))).fv) 0)

noncomputable def nb060_alpha_dummy_044 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_003))).fv) 1)

noncomputable def nb060_alpha_dummy_045 (x : Var) (y : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

noncomputable def nb060_alpha_dummy_046 (x : Var) (y : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

noncomputable def nb060_alpha_dummy_047 : Var := (freshVar (((syn_ccompl (Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cphi (Class.cv (nb060_alpha_dummy_044)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb060_alpha_dummy_048 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb060_alpha_dummy_049 : Var := (freshVar (((Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cphi (Class.cv (nb060_alpha_dummy_044))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cphi (Class.cv (nb060_alpha_dummy_044))))))).fv) 0)

noncomputable def nb060_alpha_dummy_050 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))))))).fv) 0)

noncomputable def nb060_alpha_dummy_051 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_044))).fv) 0)

noncomputable def nb060_alpha_dummy_052 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_044))).fv) 1)

noncomputable def nb060_alpha_dummy_053 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_046 x y))).fv) 0)

noncomputable def nb060_alpha_dummy_054 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_046 x y))).fv) 1)

noncomputable def nb060_alpha_dummy_055 : Var := (freshVar (((Wff.classMem (Class.cv (nb060_alpha_dummy_051)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_051)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_051))).fv) 0)

noncomputable def nb060_alpha_dummy_056 (x : Var) (y : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb060_alpha_dummy_053 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_053 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_053 x y))).fv) 0)

noncomputable def nb060_alpha_dummy_057 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb060_alpha_dummy_058 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb060_alpha_dummy_059 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb060_alpha_dummy_060 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb060_alpha_dummy_061 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb060_alpha_dummy_062 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb060_alpha_dummy_063 : Var := (freshVar (((syn_cnin (Class.cv (nb060_alpha_dummy_058)) (Class.cv (nb060_alpha_dummy_059)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_058)) (Class.cv (nb060_alpha_dummy_059)))).fv) 0)

noncomputable def nb060_alpha_dummy_064 (x : Var) (y : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb060_alpha_dummy_061 x y)) (Class.cv (nb060_alpha_dummy_062 x y)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_061 x y)) (Class.cv (nb060_alpha_dummy_062 x y)))).fv) 0)

noncomputable def nb060_alpha_dummy_065 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_058))).fv ∪ ((Class.cv (nb060_alpha_dummy_059))).fv) 0)

noncomputable def nb060_alpha_dummy_066 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_061 x y))).fv ∪ ((Class.cv (nb060_alpha_dummy_062 x y))).fv) 0)

noncomputable def nb060_alpha_dummy_067 : Var := (freshVar (((syn_ccompl (Class.cv (nb060_alpha_dummy_058)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_059)))).fv) 0)

noncomputable def nb060_alpha_dummy_068 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb060_alpha_dummy_061 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_062 x y)))).fv) 0)

noncomputable def nb060_alpha_dummy_069 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_058))).fv ∪ ((Class.cv (nb060_alpha_dummy_058))).fv) 0)

noncomputable def nb060_alpha_dummy_070 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_061 x y))).fv ∪ ((Class.cv (nb060_alpha_dummy_061 x y))).fv) 0)

noncomputable def nb060_alpha_dummy_071 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_059))).fv ∪ ((Class.cv (nb060_alpha_dummy_059))).fv) 0)

noncomputable def nb060_alpha_dummy_072 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_062 x y))).fv ∪ ((Class.cv (nb060_alpha_dummy_062 x y))).fv) 0)

noncomputable def nb060_alpha_dummy_073 : Var := (freshVar (((Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb060_alpha_dummy_074 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb060_alpha_dummy_075 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_044))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb060_alpha_dummy_076 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb060_alpha_dummy_077 : Var := (freshVar (((syn_cphi (Class.cv (nb060_alpha_dummy_044)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_044)))).fv) 0)

noncomputable def nb060_alpha_dummy_078 (x : Var) (y : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))).fv) 0)

noncomputable def nb060_alpha_dummy_079 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_003))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) 0)

noncomputable def nb060_alpha_dummy_080 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_003))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) 1)

noncomputable def nb060_alpha_dummy_081 (y : Var) (z : Var) : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 0)

noncomputable def nb060_alpha_dummy_082 (y : Var) (z : Var) : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 1)

noncomputable def nb060_alpha_dummy_083 : Var := (freshVar (((syn_ccompl (Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cphi (Class.cv (nb060_alpha_dummy_080)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb060_alpha_dummy_084 (y : Var) (z : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb060_alpha_dummy_085 : Var := (freshVar (((Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cphi (Class.cv (nb060_alpha_dummy_080))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cphi (Class.cv (nb060_alpha_dummy_080))))))).fv) 0)

noncomputable def nb060_alpha_dummy_086 (y : Var) (z : Var) : Var := (freshVar (((Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))))))).fv) 0)

noncomputable def nb060_alpha_dummy_087 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_080))).fv) 0)

noncomputable def nb060_alpha_dummy_088 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_080))).fv) 1)

noncomputable def nb060_alpha_dummy_089 (y : Var) (z : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_082 y z))).fv) 0)

noncomputable def nb060_alpha_dummy_090 (y : Var) (z : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_082 y z))).fv) 1)

noncomputable def nb060_alpha_dummy_091 : Var := (freshVar (((Wff.classMem (Class.cv (nb060_alpha_dummy_087)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_087)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_087))).fv) 0)

noncomputable def nb060_alpha_dummy_092 (y : Var) (z : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb060_alpha_dummy_089 y z)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_089 y z)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_089 y z))).fv) 0)

noncomputable def nb060_alpha_dummy_093 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb060_alpha_dummy_094 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb060_alpha_dummy_095 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb060_alpha_dummy_096 (y : Var) (z : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb060_alpha_dummy_097 (y : Var) (z : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb060_alpha_dummy_098 (y : Var) (z : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb060_alpha_dummy_099 : Var := (freshVar (((syn_cnin (Class.cv (nb060_alpha_dummy_094)) (Class.cv (nb060_alpha_dummy_095)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_094)) (Class.cv (nb060_alpha_dummy_095)))).fv) 0)

noncomputable def nb060_alpha_dummy_100 (y : Var) (z : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb060_alpha_dummy_097 y z)) (Class.cv (nb060_alpha_dummy_098 y z)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_097 y z)) (Class.cv (nb060_alpha_dummy_098 y z)))).fv) 0)

noncomputable def nb060_alpha_dummy_101 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_094))).fv ∪ ((Class.cv (nb060_alpha_dummy_095))).fv) 0)

noncomputable def nb060_alpha_dummy_102 (y : Var) (z : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_097 y z))).fv ∪ ((Class.cv (nb060_alpha_dummy_098 y z))).fv) 0)

noncomputable def nb060_alpha_dummy_103 : Var := (freshVar (((syn_ccompl (Class.cv (nb060_alpha_dummy_094)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_095)))).fv) 0)

noncomputable def nb060_alpha_dummy_104 (y : Var) (z : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb060_alpha_dummy_097 y z)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_098 y z)))).fv) 0)

noncomputable def nb060_alpha_dummy_105 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_094))).fv ∪ ((Class.cv (nb060_alpha_dummy_094))).fv) 0)

noncomputable def nb060_alpha_dummy_106 (y : Var) (z : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_097 y z))).fv ∪ ((Class.cv (nb060_alpha_dummy_097 y z))).fv) 0)

noncomputable def nb060_alpha_dummy_107 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_095))).fv ∪ ((Class.cv (nb060_alpha_dummy_095))).fv) 0)

noncomputable def nb060_alpha_dummy_108 (y : Var) (z : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_098 y z))).fv ∪ ((Class.cv (nb060_alpha_dummy_098 y z))).fv) 0)

noncomputable def nb060_alpha_dummy_109 : Var := (freshVar (((Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb060_alpha_dummy_110 (y : Var) (z : Var) : Var := (freshVar (((Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb060_alpha_dummy_111 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_080))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb060_alpha_dummy_112 (y : Var) (z : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb060_alpha_dummy_113 : Var := (freshVar (((syn_cphi (Class.cv (nb060_alpha_dummy_080)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_080)))).fv) 0)

noncomputable def nb060_alpha_dummy_114 (y : Var) (z : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))).fv) 0)

noncomputable def nb060_alpha_dummy_115 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) 0)

noncomputable def nb060_alpha_dummy_116 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) 1)

noncomputable def nb060_alpha_dummy_117 (x : Var) (z : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv z)).fv) 0)

noncomputable def nb060_alpha_dummy_118 (x : Var) (z : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv z)).fv) 1)

noncomputable def nb060_alpha_dummy_119 : Var := (freshVar (((syn_ccompl (Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cphi (Class.cv (nb060_alpha_dummy_116)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb060_alpha_dummy_120 (x : Var) (z : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb060_alpha_dummy_121 : Var := (freshVar (((Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cphi (Class.cv (nb060_alpha_dummy_116))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cphi (Class.cv (nb060_alpha_dummy_116))))))).fv) 0)

noncomputable def nb060_alpha_dummy_122 (x : Var) (z : Var) : Var := (freshVar (((Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))))))).fv) 0)

noncomputable def nb060_alpha_dummy_123 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_116))).fv) 0)

noncomputable def nb060_alpha_dummy_124 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_116))).fv) 1)

noncomputable def nb060_alpha_dummy_125 (x : Var) (z : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_118 x z))).fv) 0)

noncomputable def nb060_alpha_dummy_126 (x : Var) (z : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_118 x z))).fv) 1)

noncomputable def nb060_alpha_dummy_127 : Var := (freshVar (((Wff.classMem (Class.cv (nb060_alpha_dummy_123)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_123)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_123))).fv) 0)

noncomputable def nb060_alpha_dummy_128 (x : Var) (z : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb060_alpha_dummy_125 x z)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_125 x z)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_125 x z))).fv) 0)

noncomputable def nb060_alpha_dummy_129 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb060_alpha_dummy_130 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb060_alpha_dummy_131 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb060_alpha_dummy_132 (x : Var) (z : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb060_alpha_dummy_133 (x : Var) (z : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb060_alpha_dummy_134 (x : Var) (z : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb060_alpha_dummy_135 : Var := (freshVar (((syn_cnin (Class.cv (nb060_alpha_dummy_130)) (Class.cv (nb060_alpha_dummy_131)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_130)) (Class.cv (nb060_alpha_dummy_131)))).fv) 0)

noncomputable def nb060_alpha_dummy_136 (x : Var) (z : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb060_alpha_dummy_133 x z)) (Class.cv (nb060_alpha_dummy_134 x z)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_133 x z)) (Class.cv (nb060_alpha_dummy_134 x z)))).fv) 0)

noncomputable def nb060_alpha_dummy_137 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_130))).fv ∪ ((Class.cv (nb060_alpha_dummy_131))).fv) 0)

noncomputable def nb060_alpha_dummy_138 (x : Var) (z : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_133 x z))).fv ∪ ((Class.cv (nb060_alpha_dummy_134 x z))).fv) 0)

noncomputable def nb060_alpha_dummy_139 : Var := (freshVar (((syn_ccompl (Class.cv (nb060_alpha_dummy_130)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_131)))).fv) 0)

noncomputable def nb060_alpha_dummy_140 (x : Var) (z : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb060_alpha_dummy_133 x z)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_134 x z)))).fv) 0)

noncomputable def nb060_alpha_dummy_141 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_130))).fv ∪ ((Class.cv (nb060_alpha_dummy_130))).fv) 0)

noncomputable def nb060_alpha_dummy_142 (x : Var) (z : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_133 x z))).fv ∪ ((Class.cv (nb060_alpha_dummy_133 x z))).fv) 0)

noncomputable def nb060_alpha_dummy_143 : Var := (freshVar (((Class.cv (nb060_alpha_dummy_131))).fv ∪ ((Class.cv (nb060_alpha_dummy_131))).fv) 0)

noncomputable def nb060_alpha_dummy_144 (x : Var) (z : Var) : Var := (freshVar (((Class.cv (nb060_alpha_dummy_134 x z))).fv ∪ ((Class.cv (nb060_alpha_dummy_134 x z))).fv) 0)

noncomputable def nb060_alpha_dummy_145 : Var := (freshVar (((Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb060_alpha_dummy_146 (x : Var) (z : Var) : Var := (freshVar (((Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb060_alpha_dummy_147 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_116))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb060_alpha_dummy_148 (x : Var) (z : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb060_alpha_dummy_149 : Var := (freshVar (((syn_cphi (Class.cv (nb060_alpha_dummy_116)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_116)))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
