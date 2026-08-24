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

noncomputable def nb065_alpha_dummy_000 : Var := (freshVar ((∅ : Finset Var)) 0)

noncomputable def nb065_alpha_dummy_001 : Var := (freshVar ((∅ : Finset Var)) 1)

noncomputable def nb065_alpha_dummy_002 : Var := (freshVar ((∅ : Finset Var)) 2)

noncomputable def nb065_alpha_dummy_003 : Var := (freshVar ((∅ : Finset Var)) 3)

noncomputable def nb065_alpha_dummy_004 : Var := (freshVar (({(nb065_alpha_dummy_001)} : Finset Var) ∪ ({(nb065_alpha_dummy_000)} : Finset Var) ∪ ((syn_wral (nb065_alpha_dummy_002) (Class.cv (nb065_alpha_dummy_000)) (syn_wral (nb065_alpha_dummy_003) (Class.cv (nb065_alpha_dummy_000)) (Wff.imp (syn_wbr (Class.cv (nb065_alpha_dummy_002)) (Class.cv (nb065_alpha_dummy_001)) (Class.cv (nb065_alpha_dummy_003))) (syn_wbr (Class.cv (nb065_alpha_dummy_003)) (Class.cv (nb065_alpha_dummy_001)) (Class.cv (nb065_alpha_dummy_002))))))).fv) 0)

noncomputable def nb065_alpha_dummy_005 (x : Var) (y : Var) (r : Var) (a : Var) : Var := (freshVar (({r} : Finset Var) ∪ ({a} : Finset Var) ∪ ((syn_wral x (Class.cv a) (syn_wral y (Class.cv a) (Wff.imp (syn_wbr (Class.cv x) (Class.cv r) (Class.cv y)) (syn_wbr (Class.cv y) (Class.cv r) (Class.cv x)))))).fv) 0)

noncomputable def nb065_alpha_dummy_006 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_001))).fv ∪ ((Class.cv (nb065_alpha_dummy_000))).fv) 0)

noncomputable def nb065_alpha_dummy_007 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_001))).fv ∪ ((Class.cv (nb065_alpha_dummy_000))).fv) 1)

noncomputable def nb065_alpha_dummy_008 (r : Var) (a : Var) : Var := (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0)

noncomputable def nb065_alpha_dummy_009 (r : Var) (a : Var) : Var := (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1)

noncomputable def nb065_alpha_dummy_010 : Var := (freshVar (((syn_ccompl (Class.cab (nb065_alpha_dummy_006) (syn_wrex (nb065_alpha_dummy_007) (Class.cv (nb065_alpha_dummy_001)) (Wff.classEq (Class.cv (nb065_alpha_dummy_006)) (syn_cphi (Class.cv (nb065_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl (Class.cab (nb065_alpha_dummy_006) (syn_wrex (nb065_alpha_dummy_007) (Class.cv (nb065_alpha_dummy_000)) (Wff.classEq (Class.cv (nb065_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_007))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb065_alpha_dummy_011 (r : Var) (a : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb065_alpha_dummy_008 r a) (syn_wrex (nb065_alpha_dummy_009 r a) (Class.cv r) (Wff.classEq (Class.cv (nb065_alpha_dummy_008 r a)) (syn_cphi (Class.cv (nb065_alpha_dummy_009 r a)))))))).fv ∪ ((syn_ccompl (Class.cab (nb065_alpha_dummy_008 r a) (syn_wrex (nb065_alpha_dummy_009 r a) (Class.cv a) (Wff.classEq (Class.cv (nb065_alpha_dummy_008 r a)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_009 r a))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb065_alpha_dummy_012 : Var := (freshVar (((Class.cab (nb065_alpha_dummy_006) (syn_wrex (nb065_alpha_dummy_007) (Class.cv (nb065_alpha_dummy_001)) (Wff.classEq (Class.cv (nb065_alpha_dummy_006)) (syn_cphi (Class.cv (nb065_alpha_dummy_007))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_006) (syn_wrex (nb065_alpha_dummy_007) (Class.cv (nb065_alpha_dummy_001)) (Wff.classEq (Class.cv (nb065_alpha_dummy_006)) (syn_cphi (Class.cv (nb065_alpha_dummy_007))))))).fv) 0)

noncomputable def nb065_alpha_dummy_013 (r : Var) (a : Var) : Var := (freshVar (((Class.cab (nb065_alpha_dummy_008 r a) (syn_wrex (nb065_alpha_dummy_009 r a) (Class.cv r) (Wff.classEq (Class.cv (nb065_alpha_dummy_008 r a)) (syn_cphi (Class.cv (nb065_alpha_dummy_009 r a))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_008 r a) (syn_wrex (nb065_alpha_dummy_009 r a) (Class.cv r) (Wff.classEq (Class.cv (nb065_alpha_dummy_008 r a)) (syn_cphi (Class.cv (nb065_alpha_dummy_009 r a))))))).fv) 0)

noncomputable def nb065_alpha_dummy_014 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_007))).fv) 0)

noncomputable def nb065_alpha_dummy_015 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_007))).fv) 1)

noncomputable def nb065_alpha_dummy_016 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb065_alpha_dummy_009 r a))).fv) 0)

noncomputable def nb065_alpha_dummy_017 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb065_alpha_dummy_009 r a))).fv) 1)

noncomputable def nb065_alpha_dummy_018 : Var := (freshVar (((Wff.classMem (Class.cv (nb065_alpha_dummy_014)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb065_alpha_dummy_014)) (syn_c1c))).fv ∪ ((Class.cv (nb065_alpha_dummy_014))).fv) 0)

noncomputable def nb065_alpha_dummy_019 (r : Var) (a : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb065_alpha_dummy_016 r a)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb065_alpha_dummy_016 r a)) (syn_c1c))).fv ∪ ((Class.cv (nb065_alpha_dummy_016 r a))).fv) 0)

noncomputable def nb065_alpha_dummy_020 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb065_alpha_dummy_021 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb065_alpha_dummy_022 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb065_alpha_dummy_023 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb065_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb065_alpha_dummy_024 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb065_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb065_alpha_dummy_025 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb065_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb065_alpha_dummy_026 : Var := (freshVar (((syn_cnin (Class.cv (nb065_alpha_dummy_021)) (Class.cv (nb065_alpha_dummy_022)))).fv ∪ ((syn_cnin (Class.cv (nb065_alpha_dummy_021)) (Class.cv (nb065_alpha_dummy_022)))).fv) 0)

noncomputable def nb065_alpha_dummy_027 (r : Var) (a : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb065_alpha_dummy_024 r a)) (Class.cv (nb065_alpha_dummy_025 r a)))).fv ∪ ((syn_cnin (Class.cv (nb065_alpha_dummy_024 r a)) (Class.cv (nb065_alpha_dummy_025 r a)))).fv) 0)

noncomputable def nb065_alpha_dummy_028 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_021))).fv ∪ ((Class.cv (nb065_alpha_dummy_022))).fv) 0)

noncomputable def nb065_alpha_dummy_029 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb065_alpha_dummy_024 r a))).fv ∪ ((Class.cv (nb065_alpha_dummy_025 r a))).fv) 0)

noncomputable def nb065_alpha_dummy_030 : Var := (freshVar (((syn_ccompl (Class.cv (nb065_alpha_dummy_021)))).fv ∪ ((syn_ccompl (Class.cv (nb065_alpha_dummy_022)))).fv) 0)

noncomputable def nb065_alpha_dummy_031 (r : Var) (a : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb065_alpha_dummy_024 r a)))).fv ∪ ((syn_ccompl (Class.cv (nb065_alpha_dummy_025 r a)))).fv) 0)

noncomputable def nb065_alpha_dummy_032 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_021))).fv ∪ ((Class.cv (nb065_alpha_dummy_021))).fv) 0)

noncomputable def nb065_alpha_dummy_033 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb065_alpha_dummy_024 r a))).fv ∪ ((Class.cv (nb065_alpha_dummy_024 r a))).fv) 0)

noncomputable def nb065_alpha_dummy_034 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_022))).fv ∪ ((Class.cv (nb065_alpha_dummy_022))).fv) 0)

noncomputable def nb065_alpha_dummy_035 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb065_alpha_dummy_025 r a))).fv ∪ ((Class.cv (nb065_alpha_dummy_025 r a))).fv) 0)

noncomputable def nb065_alpha_dummy_036 : Var := (freshVar (((Class.cab (nb065_alpha_dummy_006) (syn_wrex (nb065_alpha_dummy_007) (Class.cv (nb065_alpha_dummy_000)) (Wff.classEq (Class.cv (nb065_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_007))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_006) (syn_wrex (nb065_alpha_dummy_007) (Class.cv (nb065_alpha_dummy_000)) (Wff.classEq (Class.cv (nb065_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_007))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb065_alpha_dummy_037 (r : Var) (a : Var) : Var := (freshVar (((Class.cab (nb065_alpha_dummy_008 r a) (syn_wrex (nb065_alpha_dummy_009 r a) (Class.cv a) (Wff.classEq (Class.cv (nb065_alpha_dummy_008 r a)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_009 r a))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_008 r a) (syn_wrex (nb065_alpha_dummy_009 r a) (Class.cv a) (Wff.classEq (Class.cv (nb065_alpha_dummy_008 r a)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_009 r a))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb065_alpha_dummy_038 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb065_alpha_dummy_007))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb065_alpha_dummy_039 (r : Var) (a : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb065_alpha_dummy_009 r a))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb065_alpha_dummy_040 : Var := (freshVar (((syn_cphi (Class.cv (nb065_alpha_dummy_007)))).fv ∪ ((syn_cphi (Class.cv (nb065_alpha_dummy_007)))).fv) 0)

noncomputable def nb065_alpha_dummy_041 (r : Var) (a : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb065_alpha_dummy_009 r a)))).fv ∪ ((syn_cphi (Class.cv (nb065_alpha_dummy_009 r a)))).fv) 0)

noncomputable def nb065_alpha_dummy_042 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_002))).fv ∪ ((Class.cv (nb065_alpha_dummy_003))).fv) 0)

noncomputable def nb065_alpha_dummy_043 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_002))).fv ∪ ((Class.cv (nb065_alpha_dummy_003))).fv) 1)

noncomputable def nb065_alpha_dummy_044 (x : Var) (y : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

noncomputable def nb065_alpha_dummy_045 (x : Var) (y : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

noncomputable def nb065_alpha_dummy_046 : Var := (freshVar (((syn_ccompl (Class.cab (nb065_alpha_dummy_042) (syn_wrex (nb065_alpha_dummy_043) (Class.cv (nb065_alpha_dummy_002)) (Wff.classEq (Class.cv (nb065_alpha_dummy_042)) (syn_cphi (Class.cv (nb065_alpha_dummy_043)))))))).fv ∪ ((syn_ccompl (Class.cab (nb065_alpha_dummy_042) (syn_wrex (nb065_alpha_dummy_043) (Class.cv (nb065_alpha_dummy_003)) (Wff.classEq (Class.cv (nb065_alpha_dummy_042)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_043))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb065_alpha_dummy_047 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb065_alpha_dummy_044 x y) (syn_wrex (nb065_alpha_dummy_045 x y) (Class.cv x) (Wff.classEq (Class.cv (nb065_alpha_dummy_044 x y)) (syn_cphi (Class.cv (nb065_alpha_dummy_045 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb065_alpha_dummy_044 x y) (syn_wrex (nb065_alpha_dummy_045 x y) (Class.cv y) (Wff.classEq (Class.cv (nb065_alpha_dummy_044 x y)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_045 x y))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb065_alpha_dummy_048 : Var := (freshVar (((Class.cab (nb065_alpha_dummy_042) (syn_wrex (nb065_alpha_dummy_043) (Class.cv (nb065_alpha_dummy_002)) (Wff.classEq (Class.cv (nb065_alpha_dummy_042)) (syn_cphi (Class.cv (nb065_alpha_dummy_043))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_042) (syn_wrex (nb065_alpha_dummy_043) (Class.cv (nb065_alpha_dummy_002)) (Wff.classEq (Class.cv (nb065_alpha_dummy_042)) (syn_cphi (Class.cv (nb065_alpha_dummy_043))))))).fv) 0)

noncomputable def nb065_alpha_dummy_049 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb065_alpha_dummy_044 x y) (syn_wrex (nb065_alpha_dummy_045 x y) (Class.cv x) (Wff.classEq (Class.cv (nb065_alpha_dummy_044 x y)) (syn_cphi (Class.cv (nb065_alpha_dummy_045 x y))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_044 x y) (syn_wrex (nb065_alpha_dummy_045 x y) (Class.cv x) (Wff.classEq (Class.cv (nb065_alpha_dummy_044 x y)) (syn_cphi (Class.cv (nb065_alpha_dummy_045 x y))))))).fv) 0)

noncomputable def nb065_alpha_dummy_050 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_043))).fv) 0)

noncomputable def nb065_alpha_dummy_051 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_043))).fv) 1)

noncomputable def nb065_alpha_dummy_052 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb065_alpha_dummy_045 x y))).fv) 0)

noncomputable def nb065_alpha_dummy_053 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb065_alpha_dummy_045 x y))).fv) 1)

noncomputable def nb065_alpha_dummy_054 : Var := (freshVar (((Wff.classMem (Class.cv (nb065_alpha_dummy_050)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb065_alpha_dummy_050)) (syn_c1c))).fv ∪ ((Class.cv (nb065_alpha_dummy_050))).fv) 0)

noncomputable def nb065_alpha_dummy_055 (x : Var) (y : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb065_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb065_alpha_dummy_052 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb065_alpha_dummy_052 x y))).fv) 0)

noncomputable def nb065_alpha_dummy_056 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb065_alpha_dummy_057 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb065_alpha_dummy_058 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb065_alpha_dummy_059 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb065_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb065_alpha_dummy_060 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb065_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb065_alpha_dummy_061 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb065_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb065_alpha_dummy_062 : Var := (freshVar (((syn_cnin (Class.cv (nb065_alpha_dummy_057)) (Class.cv (nb065_alpha_dummy_058)))).fv ∪ ((syn_cnin (Class.cv (nb065_alpha_dummy_057)) (Class.cv (nb065_alpha_dummy_058)))).fv) 0)

noncomputable def nb065_alpha_dummy_063 (x : Var) (y : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb065_alpha_dummy_060 x y)) (Class.cv (nb065_alpha_dummy_061 x y)))).fv ∪ ((syn_cnin (Class.cv (nb065_alpha_dummy_060 x y)) (Class.cv (nb065_alpha_dummy_061 x y)))).fv) 0)

noncomputable def nb065_alpha_dummy_064 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_057))).fv ∪ ((Class.cv (nb065_alpha_dummy_058))).fv) 0)

noncomputable def nb065_alpha_dummy_065 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb065_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb065_alpha_dummy_061 x y))).fv) 0)

noncomputable def nb065_alpha_dummy_066 : Var := (freshVar (((syn_ccompl (Class.cv (nb065_alpha_dummy_057)))).fv ∪ ((syn_ccompl (Class.cv (nb065_alpha_dummy_058)))).fv) 0)

noncomputable def nb065_alpha_dummy_067 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb065_alpha_dummy_060 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb065_alpha_dummy_061 x y)))).fv) 0)

noncomputable def nb065_alpha_dummy_068 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_057))).fv ∪ ((Class.cv (nb065_alpha_dummy_057))).fv) 0)

noncomputable def nb065_alpha_dummy_069 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb065_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb065_alpha_dummy_060 x y))).fv) 0)

noncomputable def nb065_alpha_dummy_070 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_058))).fv ∪ ((Class.cv (nb065_alpha_dummy_058))).fv) 0)

noncomputable def nb065_alpha_dummy_071 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb065_alpha_dummy_061 x y))).fv ∪ ((Class.cv (nb065_alpha_dummy_061 x y))).fv) 0)

noncomputable def nb065_alpha_dummy_072 : Var := (freshVar (((Class.cab (nb065_alpha_dummy_042) (syn_wrex (nb065_alpha_dummy_043) (Class.cv (nb065_alpha_dummy_003)) (Wff.classEq (Class.cv (nb065_alpha_dummy_042)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_043))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_042) (syn_wrex (nb065_alpha_dummy_043) (Class.cv (nb065_alpha_dummy_003)) (Wff.classEq (Class.cv (nb065_alpha_dummy_042)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_043))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb065_alpha_dummy_073 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb065_alpha_dummy_044 x y) (syn_wrex (nb065_alpha_dummy_045 x y) (Class.cv y) (Wff.classEq (Class.cv (nb065_alpha_dummy_044 x y)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_045 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_044 x y) (syn_wrex (nb065_alpha_dummy_045 x y) (Class.cv y) (Wff.classEq (Class.cv (nb065_alpha_dummy_044 x y)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_045 x y))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb065_alpha_dummy_074 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb065_alpha_dummy_043))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb065_alpha_dummy_075 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb065_alpha_dummy_045 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb065_alpha_dummy_076 : Var := (freshVar (((syn_cphi (Class.cv (nb065_alpha_dummy_043)))).fv ∪ ((syn_cphi (Class.cv (nb065_alpha_dummy_043)))).fv) 0)

noncomputable def nb065_alpha_dummy_077 (x : Var) (y : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb065_alpha_dummy_045 x y)))).fv ∪ ((syn_cphi (Class.cv (nb065_alpha_dummy_045 x y)))).fv) 0)

noncomputable def nb065_alpha_dummy_078 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_003))).fv ∪ ((Class.cv (nb065_alpha_dummy_002))).fv) 0)

noncomputable def nb065_alpha_dummy_079 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_003))).fv ∪ ((Class.cv (nb065_alpha_dummy_002))).fv) 1)

noncomputable def nb065_alpha_dummy_080 (x : Var) (y : Var) : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 0)

noncomputable def nb065_alpha_dummy_081 (x : Var) (y : Var) : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 1)

noncomputable def nb065_alpha_dummy_082 : Var := (freshVar (((syn_ccompl (Class.cab (nb065_alpha_dummy_078) (syn_wrex (nb065_alpha_dummy_079) (Class.cv (nb065_alpha_dummy_003)) (Wff.classEq (Class.cv (nb065_alpha_dummy_078)) (syn_cphi (Class.cv (nb065_alpha_dummy_079)))))))).fv ∪ ((syn_ccompl (Class.cab (nb065_alpha_dummy_078) (syn_wrex (nb065_alpha_dummy_079) (Class.cv (nb065_alpha_dummy_002)) (Wff.classEq (Class.cv (nb065_alpha_dummy_078)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_079))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb065_alpha_dummy_083 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb065_alpha_dummy_080 x y) (syn_wrex (nb065_alpha_dummy_081 x y) (Class.cv y) (Wff.classEq (Class.cv (nb065_alpha_dummy_080 x y)) (syn_cphi (Class.cv (nb065_alpha_dummy_081 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb065_alpha_dummy_080 x y) (syn_wrex (nb065_alpha_dummy_081 x y) (Class.cv x) (Wff.classEq (Class.cv (nb065_alpha_dummy_080 x y)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_081 x y))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb065_alpha_dummy_084 : Var := (freshVar (((Class.cab (nb065_alpha_dummy_078) (syn_wrex (nb065_alpha_dummy_079) (Class.cv (nb065_alpha_dummy_003)) (Wff.classEq (Class.cv (nb065_alpha_dummy_078)) (syn_cphi (Class.cv (nb065_alpha_dummy_079))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_078) (syn_wrex (nb065_alpha_dummy_079) (Class.cv (nb065_alpha_dummy_003)) (Wff.classEq (Class.cv (nb065_alpha_dummy_078)) (syn_cphi (Class.cv (nb065_alpha_dummy_079))))))).fv) 0)

noncomputable def nb065_alpha_dummy_085 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb065_alpha_dummy_080 x y) (syn_wrex (nb065_alpha_dummy_081 x y) (Class.cv y) (Wff.classEq (Class.cv (nb065_alpha_dummy_080 x y)) (syn_cphi (Class.cv (nb065_alpha_dummy_081 x y))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_080 x y) (syn_wrex (nb065_alpha_dummy_081 x y) (Class.cv y) (Wff.classEq (Class.cv (nb065_alpha_dummy_080 x y)) (syn_cphi (Class.cv (nb065_alpha_dummy_081 x y))))))).fv) 0)

noncomputable def nb065_alpha_dummy_086 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_079))).fv) 0)

noncomputable def nb065_alpha_dummy_087 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_079))).fv) 1)

noncomputable def nb065_alpha_dummy_088 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb065_alpha_dummy_081 x y))).fv) 0)

noncomputable def nb065_alpha_dummy_089 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb065_alpha_dummy_081 x y))).fv) 1)

noncomputable def nb065_alpha_dummy_090 : Var := (freshVar (((Wff.classMem (Class.cv (nb065_alpha_dummy_086)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb065_alpha_dummy_086)) (syn_c1c))).fv ∪ ((Class.cv (nb065_alpha_dummy_086))).fv) 0)

noncomputable def nb065_alpha_dummy_091 (x : Var) (y : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb065_alpha_dummy_088 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb065_alpha_dummy_088 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb065_alpha_dummy_088 x y))).fv) 0)

noncomputable def nb065_alpha_dummy_092 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb065_alpha_dummy_093 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb065_alpha_dummy_094 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb065_alpha_dummy_095 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb065_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb065_alpha_dummy_096 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb065_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb065_alpha_dummy_097 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb065_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb065_alpha_dummy_098 : Var := (freshVar (((syn_cnin (Class.cv (nb065_alpha_dummy_093)) (Class.cv (nb065_alpha_dummy_094)))).fv ∪ ((syn_cnin (Class.cv (nb065_alpha_dummy_093)) (Class.cv (nb065_alpha_dummy_094)))).fv) 0)

noncomputable def nb065_alpha_dummy_099 (x : Var) (y : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb065_alpha_dummy_096 x y)) (Class.cv (nb065_alpha_dummy_097 x y)))).fv ∪ ((syn_cnin (Class.cv (nb065_alpha_dummy_096 x y)) (Class.cv (nb065_alpha_dummy_097 x y)))).fv) 0)

noncomputable def nb065_alpha_dummy_100 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_093))).fv ∪ ((Class.cv (nb065_alpha_dummy_094))).fv) 0)

noncomputable def nb065_alpha_dummy_101 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb065_alpha_dummy_096 x y))).fv ∪ ((Class.cv (nb065_alpha_dummy_097 x y))).fv) 0)

noncomputable def nb065_alpha_dummy_102 : Var := (freshVar (((syn_ccompl (Class.cv (nb065_alpha_dummy_093)))).fv ∪ ((syn_ccompl (Class.cv (nb065_alpha_dummy_094)))).fv) 0)

noncomputable def nb065_alpha_dummy_103 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb065_alpha_dummy_096 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb065_alpha_dummy_097 x y)))).fv) 0)

noncomputable def nb065_alpha_dummy_104 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_093))).fv ∪ ((Class.cv (nb065_alpha_dummy_093))).fv) 0)

noncomputable def nb065_alpha_dummy_105 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb065_alpha_dummy_096 x y))).fv ∪ ((Class.cv (nb065_alpha_dummy_096 x y))).fv) 0)

noncomputable def nb065_alpha_dummy_106 : Var := (freshVar (((Class.cv (nb065_alpha_dummy_094))).fv ∪ ((Class.cv (nb065_alpha_dummy_094))).fv) 0)

noncomputable def nb065_alpha_dummy_107 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb065_alpha_dummy_097 x y))).fv ∪ ((Class.cv (nb065_alpha_dummy_097 x y))).fv) 0)

noncomputable def nb065_alpha_dummy_108 : Var := (freshVar (((Class.cab (nb065_alpha_dummy_078) (syn_wrex (nb065_alpha_dummy_079) (Class.cv (nb065_alpha_dummy_002)) (Wff.classEq (Class.cv (nb065_alpha_dummy_078)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_079))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_078) (syn_wrex (nb065_alpha_dummy_079) (Class.cv (nb065_alpha_dummy_002)) (Wff.classEq (Class.cv (nb065_alpha_dummy_078)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_079))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb065_alpha_dummy_109 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb065_alpha_dummy_080 x y) (syn_wrex (nb065_alpha_dummy_081 x y) (Class.cv x) (Wff.classEq (Class.cv (nb065_alpha_dummy_080 x y)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_081 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_080 x y) (syn_wrex (nb065_alpha_dummy_081 x y) (Class.cv x) (Wff.classEq (Class.cv (nb065_alpha_dummy_080 x y)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_081 x y))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb065_alpha_dummy_110 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb065_alpha_dummy_079))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb065_alpha_dummy_111 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb065_alpha_dummy_081 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb065_alpha_dummy_112 : Var := (freshVar (((syn_cphi (Class.cv (nb065_alpha_dummy_079)))).fv ∪ ((syn_cphi (Class.cv (nb065_alpha_dummy_079)))).fv) 0)

noncomputable def nb065_alpha_dummy_113 (x : Var) (y : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb065_alpha_dummy_081 x y)))).fv ∪ ((syn_cphi (Class.cv (nb065_alpha_dummy_081 x y)))).fv) 0)

theorem nb065_fresh_000 : (nb065_alpha_dummy_036) ∉ (((Class.cab (nb065_alpha_dummy_006) (syn_wrex (nb065_alpha_dummy_007) (Class.cv (nb065_alpha_dummy_000)) (Wff.classEq (Class.cv (nb065_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_007))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_006) (syn_wrex (nb065_alpha_dummy_007) (Class.cv (nb065_alpha_dummy_000)) (Wff.classEq (Class.cv (nb065_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_007))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb065_alpha_dummy_036] using freshVar_not_mem (((Class.cab (nb065_alpha_dummy_006) (syn_wrex (nb065_alpha_dummy_007) (Class.cv (nb065_alpha_dummy_000)) (Wff.classEq (Class.cv (nb065_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_007))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_006) (syn_wrex (nb065_alpha_dummy_007) (Class.cv (nb065_alpha_dummy_000)) (Wff.classEq (Class.cv (nb065_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_007))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb065_fresh_001 : (nb065_alpha_dummy_012) ∉ (((Class.cab (nb065_alpha_dummy_006) (syn_wrex (nb065_alpha_dummy_007) (Class.cv (nb065_alpha_dummy_001)) (Wff.classEq (Class.cv (nb065_alpha_dummy_006)) (syn_cphi (Class.cv (nb065_alpha_dummy_007))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_006) (syn_wrex (nb065_alpha_dummy_007) (Class.cv (nb065_alpha_dummy_001)) (Wff.classEq (Class.cv (nb065_alpha_dummy_006)) (syn_cphi (Class.cv (nb065_alpha_dummy_007))))))).fv) := by
  simpa only [nb065_alpha_dummy_012] using freshVar_not_mem (((Class.cab (nb065_alpha_dummy_006) (syn_wrex (nb065_alpha_dummy_007) (Class.cv (nb065_alpha_dummy_001)) (Wff.classEq (Class.cv (nb065_alpha_dummy_006)) (syn_cphi (Class.cv (nb065_alpha_dummy_007))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_006) (syn_wrex (nb065_alpha_dummy_007) (Class.cv (nb065_alpha_dummy_001)) (Wff.classEq (Class.cv (nb065_alpha_dummy_006)) (syn_cphi (Class.cv (nb065_alpha_dummy_007))))))).fv) 0

theorem nb065_fresh_002 (r : Var) (a : Var) : (nb065_alpha_dummy_037 r a) ∉ (((Class.cab (nb065_alpha_dummy_008 r a) (syn_wrex (nb065_alpha_dummy_009 r a) (Class.cv a) (Wff.classEq (Class.cv (nb065_alpha_dummy_008 r a)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_009 r a))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_008 r a) (syn_wrex (nb065_alpha_dummy_009 r a) (Class.cv a) (Wff.classEq (Class.cv (nb065_alpha_dummy_008 r a)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_009 r a))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb065_alpha_dummy_037] using freshVar_not_mem (((Class.cab (nb065_alpha_dummy_008 r a) (syn_wrex (nb065_alpha_dummy_009 r a) (Class.cv a) (Wff.classEq (Class.cv (nb065_alpha_dummy_008 r a)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_009 r a))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_008 r a) (syn_wrex (nb065_alpha_dummy_009 r a) (Class.cv a) (Wff.classEq (Class.cv (nb065_alpha_dummy_008 r a)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_009 r a))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb065_fresh_003 (r : Var) (a : Var) : (nb065_alpha_dummy_013 r a) ∉ (((Class.cab (nb065_alpha_dummy_008 r a) (syn_wrex (nb065_alpha_dummy_009 r a) (Class.cv r) (Wff.classEq (Class.cv (nb065_alpha_dummy_008 r a)) (syn_cphi (Class.cv (nb065_alpha_dummy_009 r a))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_008 r a) (syn_wrex (nb065_alpha_dummy_009 r a) (Class.cv r) (Wff.classEq (Class.cv (nb065_alpha_dummy_008 r a)) (syn_cphi (Class.cv (nb065_alpha_dummy_009 r a))))))).fv) := by
  simpa only [nb065_alpha_dummy_013] using freshVar_not_mem (((Class.cab (nb065_alpha_dummy_008 r a) (syn_wrex (nb065_alpha_dummy_009 r a) (Class.cv r) (Wff.classEq (Class.cv (nb065_alpha_dummy_008 r a)) (syn_cphi (Class.cv (nb065_alpha_dummy_009 r a))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_008 r a) (syn_wrex (nb065_alpha_dummy_009 r a) (Class.cv r) (Wff.classEq (Class.cv (nb065_alpha_dummy_008 r a)) (syn_cphi (Class.cv (nb065_alpha_dummy_009 r a))))))).fv) 0

theorem nb065_fresh_004 : (nb065_alpha_dummy_048) ∉ (((Class.cab (nb065_alpha_dummy_042) (syn_wrex (nb065_alpha_dummy_043) (Class.cv (nb065_alpha_dummy_002)) (Wff.classEq (Class.cv (nb065_alpha_dummy_042)) (syn_cphi (Class.cv (nb065_alpha_dummy_043))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_042) (syn_wrex (nb065_alpha_dummy_043) (Class.cv (nb065_alpha_dummy_002)) (Wff.classEq (Class.cv (nb065_alpha_dummy_042)) (syn_cphi (Class.cv (nb065_alpha_dummy_043))))))).fv) := by
  simpa only [nb065_alpha_dummy_048] using freshVar_not_mem (((Class.cab (nb065_alpha_dummy_042) (syn_wrex (nb065_alpha_dummy_043) (Class.cv (nb065_alpha_dummy_002)) (Wff.classEq (Class.cv (nb065_alpha_dummy_042)) (syn_cphi (Class.cv (nb065_alpha_dummy_043))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_042) (syn_wrex (nb065_alpha_dummy_043) (Class.cv (nb065_alpha_dummy_002)) (Wff.classEq (Class.cv (nb065_alpha_dummy_042)) (syn_cphi (Class.cv (nb065_alpha_dummy_043))))))).fv) 0

theorem nb065_fresh_005 : (nb065_alpha_dummy_072) ∉ (((Class.cab (nb065_alpha_dummy_042) (syn_wrex (nb065_alpha_dummy_043) (Class.cv (nb065_alpha_dummy_003)) (Wff.classEq (Class.cv (nb065_alpha_dummy_042)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_043))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_042) (syn_wrex (nb065_alpha_dummy_043) (Class.cv (nb065_alpha_dummy_003)) (Wff.classEq (Class.cv (nb065_alpha_dummy_042)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_043))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb065_alpha_dummy_072] using freshVar_not_mem (((Class.cab (nb065_alpha_dummy_042) (syn_wrex (nb065_alpha_dummy_043) (Class.cv (nb065_alpha_dummy_003)) (Wff.classEq (Class.cv (nb065_alpha_dummy_042)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_043))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_042) (syn_wrex (nb065_alpha_dummy_043) (Class.cv (nb065_alpha_dummy_003)) (Wff.classEq (Class.cv (nb065_alpha_dummy_042)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_043))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb065_fresh_006 (x : Var) (y : Var) : (nb065_alpha_dummy_049 x y) ∉ (((Class.cab (nb065_alpha_dummy_044 x y) (syn_wrex (nb065_alpha_dummy_045 x y) (Class.cv x) (Wff.classEq (Class.cv (nb065_alpha_dummy_044 x y)) (syn_cphi (Class.cv (nb065_alpha_dummy_045 x y))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_044 x y) (syn_wrex (nb065_alpha_dummy_045 x y) (Class.cv x) (Wff.classEq (Class.cv (nb065_alpha_dummy_044 x y)) (syn_cphi (Class.cv (nb065_alpha_dummy_045 x y))))))).fv) := by
  simpa only [nb065_alpha_dummy_049] using freshVar_not_mem (((Class.cab (nb065_alpha_dummy_044 x y) (syn_wrex (nb065_alpha_dummy_045 x y) (Class.cv x) (Wff.classEq (Class.cv (nb065_alpha_dummy_044 x y)) (syn_cphi (Class.cv (nb065_alpha_dummy_045 x y))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_044 x y) (syn_wrex (nb065_alpha_dummy_045 x y) (Class.cv x) (Wff.classEq (Class.cv (nb065_alpha_dummy_044 x y)) (syn_cphi (Class.cv (nb065_alpha_dummy_045 x y))))))).fv) 0

theorem nb065_fresh_007 (x : Var) (y : Var) : (nb065_alpha_dummy_073 x y) ∉ (((Class.cab (nb065_alpha_dummy_044 x y) (syn_wrex (nb065_alpha_dummy_045 x y) (Class.cv y) (Wff.classEq (Class.cv (nb065_alpha_dummy_044 x y)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_045 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_044 x y) (syn_wrex (nb065_alpha_dummy_045 x y) (Class.cv y) (Wff.classEq (Class.cv (nb065_alpha_dummy_044 x y)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_045 x y))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb065_alpha_dummy_073] using freshVar_not_mem (((Class.cab (nb065_alpha_dummy_044 x y) (syn_wrex (nb065_alpha_dummy_045 x y) (Class.cv y) (Wff.classEq (Class.cv (nb065_alpha_dummy_044 x y)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_045 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_044 x y) (syn_wrex (nb065_alpha_dummy_045 x y) (Class.cv y) (Wff.classEq (Class.cv (nb065_alpha_dummy_044 x y)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_045 x y))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb065_fresh_008 : (nb065_alpha_dummy_108) ∉ (((Class.cab (nb065_alpha_dummy_078) (syn_wrex (nb065_alpha_dummy_079) (Class.cv (nb065_alpha_dummy_002)) (Wff.classEq (Class.cv (nb065_alpha_dummy_078)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_079))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_078) (syn_wrex (nb065_alpha_dummy_079) (Class.cv (nb065_alpha_dummy_002)) (Wff.classEq (Class.cv (nb065_alpha_dummy_078)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_079))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb065_alpha_dummy_108] using freshVar_not_mem (((Class.cab (nb065_alpha_dummy_078) (syn_wrex (nb065_alpha_dummy_079) (Class.cv (nb065_alpha_dummy_002)) (Wff.classEq (Class.cv (nb065_alpha_dummy_078)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_079))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_078) (syn_wrex (nb065_alpha_dummy_079) (Class.cv (nb065_alpha_dummy_002)) (Wff.classEq (Class.cv (nb065_alpha_dummy_078)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_079))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb065_fresh_009 : (nb065_alpha_dummy_084) ∉ (((Class.cab (nb065_alpha_dummy_078) (syn_wrex (nb065_alpha_dummy_079) (Class.cv (nb065_alpha_dummy_003)) (Wff.classEq (Class.cv (nb065_alpha_dummy_078)) (syn_cphi (Class.cv (nb065_alpha_dummy_079))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_078) (syn_wrex (nb065_alpha_dummy_079) (Class.cv (nb065_alpha_dummy_003)) (Wff.classEq (Class.cv (nb065_alpha_dummy_078)) (syn_cphi (Class.cv (nb065_alpha_dummy_079))))))).fv) := by
  simpa only [nb065_alpha_dummy_084] using freshVar_not_mem (((Class.cab (nb065_alpha_dummy_078) (syn_wrex (nb065_alpha_dummy_079) (Class.cv (nb065_alpha_dummy_003)) (Wff.classEq (Class.cv (nb065_alpha_dummy_078)) (syn_cphi (Class.cv (nb065_alpha_dummy_079))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_078) (syn_wrex (nb065_alpha_dummy_079) (Class.cv (nb065_alpha_dummy_003)) (Wff.classEq (Class.cv (nb065_alpha_dummy_078)) (syn_cphi (Class.cv (nb065_alpha_dummy_079))))))).fv) 0

theorem nb065_fresh_010 (x : Var) (y : Var) : (nb065_alpha_dummy_109 x y) ∉ (((Class.cab (nb065_alpha_dummy_080 x y) (syn_wrex (nb065_alpha_dummy_081 x y) (Class.cv x) (Wff.classEq (Class.cv (nb065_alpha_dummy_080 x y)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_081 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_080 x y) (syn_wrex (nb065_alpha_dummy_081 x y) (Class.cv x) (Wff.classEq (Class.cv (nb065_alpha_dummy_080 x y)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_081 x y))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb065_alpha_dummy_109] using freshVar_not_mem (((Class.cab (nb065_alpha_dummy_080 x y) (syn_wrex (nb065_alpha_dummy_081 x y) (Class.cv x) (Wff.classEq (Class.cv (nb065_alpha_dummy_080 x y)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_081 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_080 x y) (syn_wrex (nb065_alpha_dummy_081 x y) (Class.cv x) (Wff.classEq (Class.cv (nb065_alpha_dummy_080 x y)) (syn_cun (syn_cphi (Class.cv (nb065_alpha_dummy_081 x y))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb065_fresh_011 (x : Var) (y : Var) : (nb065_alpha_dummy_085 x y) ∉ (((Class.cab (nb065_alpha_dummy_080 x y) (syn_wrex (nb065_alpha_dummy_081 x y) (Class.cv y) (Wff.classEq (Class.cv (nb065_alpha_dummy_080 x y)) (syn_cphi (Class.cv (nb065_alpha_dummy_081 x y))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_080 x y) (syn_wrex (nb065_alpha_dummy_081 x y) (Class.cv y) (Wff.classEq (Class.cv (nb065_alpha_dummy_080 x y)) (syn_cphi (Class.cv (nb065_alpha_dummy_081 x y))))))).fv) := by
  simpa only [nb065_alpha_dummy_085] using freshVar_not_mem (((Class.cab (nb065_alpha_dummy_080 x y) (syn_wrex (nb065_alpha_dummy_081 x y) (Class.cv y) (Wff.classEq (Class.cv (nb065_alpha_dummy_080 x y)) (syn_cphi (Class.cv (nb065_alpha_dummy_081 x y))))))).fv ∪ ((Class.cab (nb065_alpha_dummy_080 x y) (syn_wrex (nb065_alpha_dummy_081 x y) (Class.cv y) (Wff.classEq (Class.cv (nb065_alpha_dummy_080 x y)) (syn_cphi (Class.cv (nb065_alpha_dummy_081 x y))))))).fv) 0

theorem nb065_fresh_012 : (nb065_alpha_dummy_006) ∉ (((Class.cv (nb065_alpha_dummy_001))).fv ∪ ((Class.cv (nb065_alpha_dummy_000))).fv) := by
  simpa only [nb065_alpha_dummy_006] using freshVar_not_mem (((Class.cv (nb065_alpha_dummy_001))).fv ∪ ((Class.cv (nb065_alpha_dummy_000))).fv) 0

theorem nb065_fresh_013 : (nb065_alpha_dummy_007) ∉ (((Class.cv (nb065_alpha_dummy_001))).fv ∪ ((Class.cv (nb065_alpha_dummy_000))).fv) := by
  simpa only [nb065_alpha_dummy_007] using freshVar_not_mem (((Class.cv (nb065_alpha_dummy_001))).fv ∪ ((Class.cv (nb065_alpha_dummy_000))).fv) 1

theorem nb065_distinct_014 : (nb065_alpha_dummy_006) ≠ (nb065_alpha_dummy_007) := by
  simpa only [nb065_alpha_dummy_006, nb065_alpha_dummy_007] using
    (freshVar_injective (((Class.cv (nb065_alpha_dummy_001))).fv ∪ ((Class.cv (nb065_alpha_dummy_000))).fv) (i := 0) (j := 1) (by decide))

theorem nb065_fresh_015 : (nb065_alpha_dummy_042) ∉ (((Class.cv (nb065_alpha_dummy_002))).fv ∪ ((Class.cv (nb065_alpha_dummy_003))).fv) := by
  simpa only [nb065_alpha_dummy_042] using freshVar_not_mem (((Class.cv (nb065_alpha_dummy_002))).fv ∪ ((Class.cv (nb065_alpha_dummy_003))).fv) 0

theorem nb065_fresh_016 : (nb065_alpha_dummy_043) ∉ (((Class.cv (nb065_alpha_dummy_002))).fv ∪ ((Class.cv (nb065_alpha_dummy_003))).fv) := by
  simpa only [nb065_alpha_dummy_043] using freshVar_not_mem (((Class.cv (nb065_alpha_dummy_002))).fv ∪ ((Class.cv (nb065_alpha_dummy_003))).fv) 1

theorem nb065_distinct_017 : (nb065_alpha_dummy_042) ≠ (nb065_alpha_dummy_043) := by
  simpa only [nb065_alpha_dummy_042, nb065_alpha_dummy_043] using
    (freshVar_injective (((Class.cv (nb065_alpha_dummy_002))).fv ∪ ((Class.cv (nb065_alpha_dummy_003))).fv) (i := 0) (j := 1) (by decide))

theorem nb065_fresh_018 : (nb065_alpha_dummy_078) ∉ (((Class.cv (nb065_alpha_dummy_003))).fv ∪ ((Class.cv (nb065_alpha_dummy_002))).fv) := by
  simpa only [nb065_alpha_dummy_078] using freshVar_not_mem (((Class.cv (nb065_alpha_dummy_003))).fv ∪ ((Class.cv (nb065_alpha_dummy_002))).fv) 0

theorem nb065_fresh_019 : (nb065_alpha_dummy_079) ∉ (((Class.cv (nb065_alpha_dummy_003))).fv ∪ ((Class.cv (nb065_alpha_dummy_002))).fv) := by
  simpa only [nb065_alpha_dummy_079] using freshVar_not_mem (((Class.cv (nb065_alpha_dummy_003))).fv ∪ ((Class.cv (nb065_alpha_dummy_002))).fv) 1

theorem nb065_distinct_020 : (nb065_alpha_dummy_078) ≠ (nb065_alpha_dummy_079) := by
  simpa only [nb065_alpha_dummy_078, nb065_alpha_dummy_079] using
    (freshVar_injective (((Class.cv (nb065_alpha_dummy_003))).fv ∪ ((Class.cv (nb065_alpha_dummy_002))).fv) (i := 0) (j := 1) (by decide))

theorem nb065_fresh_021 : (nb065_alpha_dummy_014) ∉ (((Class.cv (nb065_alpha_dummy_007))).fv) := by
  simpa only [nb065_alpha_dummy_014] using freshVar_not_mem (((Class.cv (nb065_alpha_dummy_007))).fv) 0

theorem nb065_fresh_022 : (nb065_alpha_dummy_015) ∉ (((Class.cv (nb065_alpha_dummy_007))).fv) := by
  simpa only [nb065_alpha_dummy_015] using freshVar_not_mem (((Class.cv (nb065_alpha_dummy_007))).fv) 1

theorem nb065_distinct_023 : (nb065_alpha_dummy_014) ≠ (nb065_alpha_dummy_015) := by
  simpa only [nb065_alpha_dummy_014, nb065_alpha_dummy_015] using
    (freshVar_injective (((Class.cv (nb065_alpha_dummy_007))).fv) (i := 0) (j := 1) (by decide))

theorem nb065_fresh_024 (r : Var) (a : Var) : (nb065_alpha_dummy_016 r a) ∉ (((Class.cv (nb065_alpha_dummy_009 r a))).fv) := by
  simpa only [nb065_alpha_dummy_016] using freshVar_not_mem (((Class.cv (nb065_alpha_dummy_009 r a))).fv) 0

theorem nb065_fresh_025 (r : Var) (a : Var) : (nb065_alpha_dummy_017 r a) ∉ (((Class.cv (nb065_alpha_dummy_009 r a))).fv) := by
  simpa only [nb065_alpha_dummy_017] using freshVar_not_mem (((Class.cv (nb065_alpha_dummy_009 r a))).fv) 1

theorem nb065_distinct_026 (r : Var) (a : Var) : (nb065_alpha_dummy_016 r a) ≠ (nb065_alpha_dummy_017 r a) := by
  simpa only [nb065_alpha_dummy_016, nb065_alpha_dummy_017] using
    (freshVar_injective (((Class.cv (nb065_alpha_dummy_009 r a))).fv) (i := 0) (j := 1) (by decide))

theorem nb065_fresh_027 : (nb065_alpha_dummy_020) ∉ (((Class.cv (nb065_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb065_alpha_dummy_020] using freshVar_not_mem (((Class.cv (nb065_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) 0

theorem nb065_fresh_028 : (nb065_alpha_dummy_021) ∉ (((Class.cv (nb065_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb065_alpha_dummy_021] using freshVar_not_mem (((Class.cv (nb065_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) 1

theorem nb065_fresh_029 : (nb065_alpha_dummy_022) ∉ (((Class.cv (nb065_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb065_alpha_dummy_022] using freshVar_not_mem (((Class.cv (nb065_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) 2

theorem nb065_distinct_030 : (nb065_alpha_dummy_020) ≠ (nb065_alpha_dummy_021) := by
  simpa only [nb065_alpha_dummy_020, nb065_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb065_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb065_distinct_031 : (nb065_alpha_dummy_020) ≠ (nb065_alpha_dummy_022) := by
  simpa only [nb065_alpha_dummy_020, nb065_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb065_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb065_distinct_032 : (nb065_alpha_dummy_021) ≠ (nb065_alpha_dummy_022) := by
  simpa only [nb065_alpha_dummy_021, nb065_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb065_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb065_fresh_033 (r : Var) (a : Var) : (nb065_alpha_dummy_023 r a) ∉ (((Class.cv (nb065_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb065_alpha_dummy_023] using freshVar_not_mem (((Class.cv (nb065_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) 0

theorem nb065_fresh_034 (r : Var) (a : Var) : (nb065_alpha_dummy_024 r a) ∉ (((Class.cv (nb065_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb065_alpha_dummy_024] using freshVar_not_mem (((Class.cv (nb065_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) 1

theorem nb065_fresh_035 (r : Var) (a : Var) : (nb065_alpha_dummy_025 r a) ∉ (((Class.cv (nb065_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb065_alpha_dummy_025] using freshVar_not_mem (((Class.cv (nb065_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) 2

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
