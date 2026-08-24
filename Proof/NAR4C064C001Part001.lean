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

noncomputable def nb064_alpha_dummy_000 : Var := (freshVar ((∅ : Finset Var)) 0)

noncomputable def nb064_alpha_dummy_001 : Var := (freshVar ((∅ : Finset Var)) 1)

noncomputable def nb064_alpha_dummy_002 : Var := (freshVar ((∅ : Finset Var)) 2)

noncomputable def nb064_alpha_dummy_003 : Var := (freshVar ((∅ : Finset Var)) 3)

noncomputable def nb064_alpha_dummy_004 : Var := (freshVar ((∅ : Finset Var)) 4)

noncomputable def nb064_alpha_dummy_005 : Var := (freshVar (({(nb064_alpha_dummy_001)} : Finset Var) ∪ ({(nb064_alpha_dummy_000)} : Finset Var) ∪ ((Wff.all (nb064_alpha_dummy_002) (Wff.imp (syn_wa (syn_wss (Class.cv (nb064_alpha_dummy_002)) (Class.cv (nb064_alpha_dummy_000))) (syn_wne (Class.cv (nb064_alpha_dummy_002)) (syn_c0))) (syn_wrex (nb064_alpha_dummy_004) (Class.cv (nb064_alpha_dummy_002)) (syn_wral (nb064_alpha_dummy_003) (Class.cv (nb064_alpha_dummy_002)) (Wff.imp (syn_wbr (Class.cv (nb064_alpha_dummy_003)) (Class.cv (nb064_alpha_dummy_001)) (Class.cv (nb064_alpha_dummy_004))) (Wff.objEq (nb064_alpha_dummy_003) (nb064_alpha_dummy_004)))))))).fv) 0)

noncomputable def nb064_alpha_dummy_006 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : Var := (freshVar (({r} : Finset Var) ∪ ({a} : Finset Var) ∪ ((Wff.all x (Wff.imp (syn_wa (syn_wss (Class.cv x) (Class.cv a)) (syn_wne (Class.cv x) (syn_c0))) (syn_wrex z (Class.cv x) (syn_wral y (Class.cv x) (Wff.imp (syn_wbr (Class.cv y) (Class.cv r) (Class.cv z)) (Wff.objEq y z))))))).fv) 0)

noncomputable def nb064_alpha_dummy_007 : Var := (freshVar (((Class.cv (nb064_alpha_dummy_001))).fv ∪ ((Class.cv (nb064_alpha_dummy_000))).fv) 0)

noncomputable def nb064_alpha_dummy_008 : Var := (freshVar (((Class.cv (nb064_alpha_dummy_001))).fv ∪ ((Class.cv (nb064_alpha_dummy_000))).fv) 1)

noncomputable def nb064_alpha_dummy_009 (r : Var) (a : Var) : Var := (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0)

noncomputable def nb064_alpha_dummy_010 (r : Var) (a : Var) : Var := (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1)

noncomputable def nb064_alpha_dummy_011 : Var := (freshVar (((syn_ccompl (Class.cab (nb064_alpha_dummy_007) (syn_wrex (nb064_alpha_dummy_008) (Class.cv (nb064_alpha_dummy_001)) (Wff.classEq (Class.cv (nb064_alpha_dummy_007)) (syn_cphi (Class.cv (nb064_alpha_dummy_008)))))))).fv ∪ ((syn_ccompl (Class.cab (nb064_alpha_dummy_007) (syn_wrex (nb064_alpha_dummy_008) (Class.cv (nb064_alpha_dummy_000)) (Wff.classEq (Class.cv (nb064_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_008))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb064_alpha_dummy_012 (r : Var) (a : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb064_alpha_dummy_009 r a) (syn_wrex (nb064_alpha_dummy_010 r a) (Class.cv r) (Wff.classEq (Class.cv (nb064_alpha_dummy_009 r a)) (syn_cphi (Class.cv (nb064_alpha_dummy_010 r a)))))))).fv ∪ ((syn_ccompl (Class.cab (nb064_alpha_dummy_009 r a) (syn_wrex (nb064_alpha_dummy_010 r a) (Class.cv a) (Wff.classEq (Class.cv (nb064_alpha_dummy_009 r a)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_010 r a))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb064_alpha_dummy_013 : Var := (freshVar (((Class.cab (nb064_alpha_dummy_007) (syn_wrex (nb064_alpha_dummy_008) (Class.cv (nb064_alpha_dummy_001)) (Wff.classEq (Class.cv (nb064_alpha_dummy_007)) (syn_cphi (Class.cv (nb064_alpha_dummy_008))))))).fv ∪ ((Class.cab (nb064_alpha_dummy_007) (syn_wrex (nb064_alpha_dummy_008) (Class.cv (nb064_alpha_dummy_001)) (Wff.classEq (Class.cv (nb064_alpha_dummy_007)) (syn_cphi (Class.cv (nb064_alpha_dummy_008))))))).fv) 0)

noncomputable def nb064_alpha_dummy_014 (r : Var) (a : Var) : Var := (freshVar (((Class.cab (nb064_alpha_dummy_009 r a) (syn_wrex (nb064_alpha_dummy_010 r a) (Class.cv r) (Wff.classEq (Class.cv (nb064_alpha_dummy_009 r a)) (syn_cphi (Class.cv (nb064_alpha_dummy_010 r a))))))).fv ∪ ((Class.cab (nb064_alpha_dummy_009 r a) (syn_wrex (nb064_alpha_dummy_010 r a) (Class.cv r) (Wff.classEq (Class.cv (nb064_alpha_dummy_009 r a)) (syn_cphi (Class.cv (nb064_alpha_dummy_010 r a))))))).fv) 0)

noncomputable def nb064_alpha_dummy_015 : Var := (freshVar (((Class.cv (nb064_alpha_dummy_008))).fv) 0)

noncomputable def nb064_alpha_dummy_016 : Var := (freshVar (((Class.cv (nb064_alpha_dummy_008))).fv) 1)

noncomputable def nb064_alpha_dummy_017 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb064_alpha_dummy_010 r a))).fv) 0)

noncomputable def nb064_alpha_dummy_018 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb064_alpha_dummy_010 r a))).fv) 1)

noncomputable def nb064_alpha_dummy_019 : Var := (freshVar (((Wff.classMem (Class.cv (nb064_alpha_dummy_015)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb064_alpha_dummy_015)) (syn_c1c))).fv ∪ ((Class.cv (nb064_alpha_dummy_015))).fv) 0)

noncomputable def nb064_alpha_dummy_020 (r : Var) (a : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb064_alpha_dummy_017 r a)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb064_alpha_dummy_017 r a)) (syn_c1c))).fv ∪ ((Class.cv (nb064_alpha_dummy_017 r a))).fv) 0)

noncomputable def nb064_alpha_dummy_021 : Var := (freshVar (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb064_alpha_dummy_022 : Var := (freshVar (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb064_alpha_dummy_023 : Var := (freshVar (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb064_alpha_dummy_024 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb064_alpha_dummy_025 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb064_alpha_dummy_026 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb064_alpha_dummy_027 : Var := (freshVar (((syn_cnin (Class.cv (nb064_alpha_dummy_022)) (Class.cv (nb064_alpha_dummy_023)))).fv ∪ ((syn_cnin (Class.cv (nb064_alpha_dummy_022)) (Class.cv (nb064_alpha_dummy_023)))).fv) 0)

noncomputable def nb064_alpha_dummy_028 (r : Var) (a : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb064_alpha_dummy_025 r a)) (Class.cv (nb064_alpha_dummy_026 r a)))).fv ∪ ((syn_cnin (Class.cv (nb064_alpha_dummy_025 r a)) (Class.cv (nb064_alpha_dummy_026 r a)))).fv) 0)

noncomputable def nb064_alpha_dummy_029 : Var := (freshVar (((Class.cv (nb064_alpha_dummy_022))).fv ∪ ((Class.cv (nb064_alpha_dummy_023))).fv) 0)

noncomputable def nb064_alpha_dummy_030 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb064_alpha_dummy_025 r a))).fv ∪ ((Class.cv (nb064_alpha_dummy_026 r a))).fv) 0)

noncomputable def nb064_alpha_dummy_031 : Var := (freshVar (((syn_ccompl (Class.cv (nb064_alpha_dummy_022)))).fv ∪ ((syn_ccompl (Class.cv (nb064_alpha_dummy_023)))).fv) 0)

noncomputable def nb064_alpha_dummy_032 (r : Var) (a : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb064_alpha_dummy_025 r a)))).fv ∪ ((syn_ccompl (Class.cv (nb064_alpha_dummy_026 r a)))).fv) 0)

noncomputable def nb064_alpha_dummy_033 : Var := (freshVar (((Class.cv (nb064_alpha_dummy_022))).fv ∪ ((Class.cv (nb064_alpha_dummy_022))).fv) 0)

noncomputable def nb064_alpha_dummy_034 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb064_alpha_dummy_025 r a))).fv ∪ ((Class.cv (nb064_alpha_dummy_025 r a))).fv) 0)

noncomputable def nb064_alpha_dummy_035 : Var := (freshVar (((Class.cv (nb064_alpha_dummy_023))).fv ∪ ((Class.cv (nb064_alpha_dummy_023))).fv) 0)

noncomputable def nb064_alpha_dummy_036 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb064_alpha_dummy_026 r a))).fv ∪ ((Class.cv (nb064_alpha_dummy_026 r a))).fv) 0)

noncomputable def nb064_alpha_dummy_037 : Var := (freshVar (((Class.cab (nb064_alpha_dummy_007) (syn_wrex (nb064_alpha_dummy_008) (Class.cv (nb064_alpha_dummy_000)) (Wff.classEq (Class.cv (nb064_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_008))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb064_alpha_dummy_007) (syn_wrex (nb064_alpha_dummy_008) (Class.cv (nb064_alpha_dummy_000)) (Wff.classEq (Class.cv (nb064_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_008))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb064_alpha_dummy_038 (r : Var) (a : Var) : Var := (freshVar (((Class.cab (nb064_alpha_dummy_009 r a) (syn_wrex (nb064_alpha_dummy_010 r a) (Class.cv a) (Wff.classEq (Class.cv (nb064_alpha_dummy_009 r a)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_010 r a))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb064_alpha_dummy_009 r a) (syn_wrex (nb064_alpha_dummy_010 r a) (Class.cv a) (Wff.classEq (Class.cv (nb064_alpha_dummy_009 r a)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_010 r a))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb064_alpha_dummy_039 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb064_alpha_dummy_008))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb064_alpha_dummy_040 (r : Var) (a : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb064_alpha_dummy_010 r a))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb064_alpha_dummy_041 : Var := (freshVar (((syn_cphi (Class.cv (nb064_alpha_dummy_008)))).fv ∪ ((syn_cphi (Class.cv (nb064_alpha_dummy_008)))).fv) 0)

noncomputable def nb064_alpha_dummy_042 (r : Var) (a : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb064_alpha_dummy_010 r a)))).fv ∪ ((syn_cphi (Class.cv (nb064_alpha_dummy_010 r a)))).fv) 0)

noncomputable def nb064_alpha_dummy_043 : Var := (freshVar (((syn_cnin (Class.cv (nb064_alpha_dummy_002)) (Class.cv (nb064_alpha_dummy_000)))).fv ∪ ((syn_cnin (Class.cv (nb064_alpha_dummy_002)) (Class.cv (nb064_alpha_dummy_000)))).fv) 0)

noncomputable def nb064_alpha_dummy_044 (x : Var) (a : Var) : Var := (freshVar (((syn_cnin (Class.cv x) (Class.cv a))).fv ∪ ((syn_cnin (Class.cv x) (Class.cv a))).fv) 0)

noncomputable def nb064_alpha_dummy_045 : Var := (freshVar (((Class.cv (nb064_alpha_dummy_002))).fv ∪ ((Class.cv (nb064_alpha_dummy_000))).fv) 0)

noncomputable def nb064_alpha_dummy_046 (x : Var) (a : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv a)).fv) 0)

noncomputable def nb064_alpha_dummy_047 : Var := (freshVar (((Class.cv (nb064_alpha_dummy_003))).fv ∪ ((Class.cv (nb064_alpha_dummy_004))).fv) 0)

noncomputable def nb064_alpha_dummy_048 : Var := (freshVar (((Class.cv (nb064_alpha_dummy_003))).fv ∪ ((Class.cv (nb064_alpha_dummy_004))).fv) 1)

noncomputable def nb064_alpha_dummy_049 (y : Var) (z : Var) : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 0)

noncomputable def nb064_alpha_dummy_050 (y : Var) (z : Var) : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 1)

noncomputable def nb064_alpha_dummy_051 : Var := (freshVar (((syn_ccompl (Class.cab (nb064_alpha_dummy_047) (syn_wrex (nb064_alpha_dummy_048) (Class.cv (nb064_alpha_dummy_003)) (Wff.classEq (Class.cv (nb064_alpha_dummy_047)) (syn_cphi (Class.cv (nb064_alpha_dummy_048)))))))).fv ∪ ((syn_ccompl (Class.cab (nb064_alpha_dummy_047) (syn_wrex (nb064_alpha_dummy_048) (Class.cv (nb064_alpha_dummy_004)) (Wff.classEq (Class.cv (nb064_alpha_dummy_047)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_048))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb064_alpha_dummy_052 (y : Var) (z : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb064_alpha_dummy_049 y z) (syn_wrex (nb064_alpha_dummy_050 y z) (Class.cv y) (Wff.classEq (Class.cv (nb064_alpha_dummy_049 y z)) (syn_cphi (Class.cv (nb064_alpha_dummy_050 y z)))))))).fv ∪ ((syn_ccompl (Class.cab (nb064_alpha_dummy_049 y z) (syn_wrex (nb064_alpha_dummy_050 y z) (Class.cv z) (Wff.classEq (Class.cv (nb064_alpha_dummy_049 y z)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_050 y z))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb064_alpha_dummy_053 : Var := (freshVar (((Class.cab (nb064_alpha_dummy_047) (syn_wrex (nb064_alpha_dummy_048) (Class.cv (nb064_alpha_dummy_003)) (Wff.classEq (Class.cv (nb064_alpha_dummy_047)) (syn_cphi (Class.cv (nb064_alpha_dummy_048))))))).fv ∪ ((Class.cab (nb064_alpha_dummy_047) (syn_wrex (nb064_alpha_dummy_048) (Class.cv (nb064_alpha_dummy_003)) (Wff.classEq (Class.cv (nb064_alpha_dummy_047)) (syn_cphi (Class.cv (nb064_alpha_dummy_048))))))).fv) 0)

noncomputable def nb064_alpha_dummy_054 (y : Var) (z : Var) : Var := (freshVar (((Class.cab (nb064_alpha_dummy_049 y z) (syn_wrex (nb064_alpha_dummy_050 y z) (Class.cv y) (Wff.classEq (Class.cv (nb064_alpha_dummy_049 y z)) (syn_cphi (Class.cv (nb064_alpha_dummy_050 y z))))))).fv ∪ ((Class.cab (nb064_alpha_dummy_049 y z) (syn_wrex (nb064_alpha_dummy_050 y z) (Class.cv y) (Wff.classEq (Class.cv (nb064_alpha_dummy_049 y z)) (syn_cphi (Class.cv (nb064_alpha_dummy_050 y z))))))).fv) 0)

noncomputable def nb064_alpha_dummy_055 : Var := (freshVar (((Class.cv (nb064_alpha_dummy_048))).fv) 0)

noncomputable def nb064_alpha_dummy_056 : Var := (freshVar (((Class.cv (nb064_alpha_dummy_048))).fv) 1)

noncomputable def nb064_alpha_dummy_057 (y : Var) (z : Var) : Var := (freshVar (((Class.cv (nb064_alpha_dummy_050 y z))).fv) 0)

noncomputable def nb064_alpha_dummy_058 (y : Var) (z : Var) : Var := (freshVar (((Class.cv (nb064_alpha_dummy_050 y z))).fv) 1)

noncomputable def nb064_alpha_dummy_059 : Var := (freshVar (((Wff.classMem (Class.cv (nb064_alpha_dummy_055)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb064_alpha_dummy_055)) (syn_c1c))).fv ∪ ((Class.cv (nb064_alpha_dummy_055))).fv) 0)

noncomputable def nb064_alpha_dummy_060 (y : Var) (z : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb064_alpha_dummy_057 y z)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb064_alpha_dummy_057 y z)) (syn_c1c))).fv ∪ ((Class.cv (nb064_alpha_dummy_057 y z))).fv) 0)

noncomputable def nb064_alpha_dummy_061 : Var := (freshVar (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb064_alpha_dummy_062 : Var := (freshVar (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb064_alpha_dummy_063 : Var := (freshVar (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb064_alpha_dummy_064 (y : Var) (z : Var) : Var := (freshVar (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb064_alpha_dummy_065 (y : Var) (z : Var) : Var := (freshVar (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb064_alpha_dummy_066 (y : Var) (z : Var) : Var := (freshVar (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb064_alpha_dummy_067 : Var := (freshVar (((syn_cnin (Class.cv (nb064_alpha_dummy_062)) (Class.cv (nb064_alpha_dummy_063)))).fv ∪ ((syn_cnin (Class.cv (nb064_alpha_dummy_062)) (Class.cv (nb064_alpha_dummy_063)))).fv) 0)

noncomputable def nb064_alpha_dummy_068 (y : Var) (z : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb064_alpha_dummy_065 y z)) (Class.cv (nb064_alpha_dummy_066 y z)))).fv ∪ ((syn_cnin (Class.cv (nb064_alpha_dummy_065 y z)) (Class.cv (nb064_alpha_dummy_066 y z)))).fv) 0)

noncomputable def nb064_alpha_dummy_069 : Var := (freshVar (((Class.cv (nb064_alpha_dummy_062))).fv ∪ ((Class.cv (nb064_alpha_dummy_063))).fv) 0)

noncomputable def nb064_alpha_dummy_070 (y : Var) (z : Var) : Var := (freshVar (((Class.cv (nb064_alpha_dummy_065 y z))).fv ∪ ((Class.cv (nb064_alpha_dummy_066 y z))).fv) 0)

noncomputable def nb064_alpha_dummy_071 : Var := (freshVar (((syn_ccompl (Class.cv (nb064_alpha_dummy_062)))).fv ∪ ((syn_ccompl (Class.cv (nb064_alpha_dummy_063)))).fv) 0)

noncomputable def nb064_alpha_dummy_072 (y : Var) (z : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb064_alpha_dummy_065 y z)))).fv ∪ ((syn_ccompl (Class.cv (nb064_alpha_dummy_066 y z)))).fv) 0)

noncomputable def nb064_alpha_dummy_073 : Var := (freshVar (((Class.cv (nb064_alpha_dummy_062))).fv ∪ ((Class.cv (nb064_alpha_dummy_062))).fv) 0)

noncomputable def nb064_alpha_dummy_074 (y : Var) (z : Var) : Var := (freshVar (((Class.cv (nb064_alpha_dummy_065 y z))).fv ∪ ((Class.cv (nb064_alpha_dummy_065 y z))).fv) 0)

noncomputable def nb064_alpha_dummy_075 : Var := (freshVar (((Class.cv (nb064_alpha_dummy_063))).fv ∪ ((Class.cv (nb064_alpha_dummy_063))).fv) 0)

noncomputable def nb064_alpha_dummy_076 (y : Var) (z : Var) : Var := (freshVar (((Class.cv (nb064_alpha_dummy_066 y z))).fv ∪ ((Class.cv (nb064_alpha_dummy_066 y z))).fv) 0)

noncomputable def nb064_alpha_dummy_077 : Var := (freshVar (((Class.cab (nb064_alpha_dummy_047) (syn_wrex (nb064_alpha_dummy_048) (Class.cv (nb064_alpha_dummy_004)) (Wff.classEq (Class.cv (nb064_alpha_dummy_047)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_048))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb064_alpha_dummy_047) (syn_wrex (nb064_alpha_dummy_048) (Class.cv (nb064_alpha_dummy_004)) (Wff.classEq (Class.cv (nb064_alpha_dummy_047)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_048))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb064_alpha_dummy_078 (y : Var) (z : Var) : Var := (freshVar (((Class.cab (nb064_alpha_dummy_049 y z) (syn_wrex (nb064_alpha_dummy_050 y z) (Class.cv z) (Wff.classEq (Class.cv (nb064_alpha_dummy_049 y z)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_050 y z))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb064_alpha_dummy_049 y z) (syn_wrex (nb064_alpha_dummy_050 y z) (Class.cv z) (Wff.classEq (Class.cv (nb064_alpha_dummy_049 y z)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_050 y z))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb064_alpha_dummy_079 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb064_alpha_dummy_048))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb064_alpha_dummy_080 (y : Var) (z : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb064_alpha_dummy_050 y z))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb064_alpha_dummy_081 : Var := (freshVar (((syn_cphi (Class.cv (nb064_alpha_dummy_048)))).fv ∪ ((syn_cphi (Class.cv (nb064_alpha_dummy_048)))).fv) 0)

noncomputable def nb064_alpha_dummy_082 (y : Var) (z : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb064_alpha_dummy_050 y z)))).fv ∪ ((syn_cphi (Class.cv (nb064_alpha_dummy_050 y z)))).fv) 0)

theorem nb064_fresh_000 : (nb064_alpha_dummy_037) ∉ (((Class.cab (nb064_alpha_dummy_007) (syn_wrex (nb064_alpha_dummy_008) (Class.cv (nb064_alpha_dummy_000)) (Wff.classEq (Class.cv (nb064_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_008))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb064_alpha_dummy_007) (syn_wrex (nb064_alpha_dummy_008) (Class.cv (nb064_alpha_dummy_000)) (Wff.classEq (Class.cv (nb064_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_008))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb064_alpha_dummy_037] using freshVar_not_mem (((Class.cab (nb064_alpha_dummy_007) (syn_wrex (nb064_alpha_dummy_008) (Class.cv (nb064_alpha_dummy_000)) (Wff.classEq (Class.cv (nb064_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_008))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb064_alpha_dummy_007) (syn_wrex (nb064_alpha_dummy_008) (Class.cv (nb064_alpha_dummy_000)) (Wff.classEq (Class.cv (nb064_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_008))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb064_fresh_001 : (nb064_alpha_dummy_013) ∉ (((Class.cab (nb064_alpha_dummy_007) (syn_wrex (nb064_alpha_dummy_008) (Class.cv (nb064_alpha_dummy_001)) (Wff.classEq (Class.cv (nb064_alpha_dummy_007)) (syn_cphi (Class.cv (nb064_alpha_dummy_008))))))).fv ∪ ((Class.cab (nb064_alpha_dummy_007) (syn_wrex (nb064_alpha_dummy_008) (Class.cv (nb064_alpha_dummy_001)) (Wff.classEq (Class.cv (nb064_alpha_dummy_007)) (syn_cphi (Class.cv (nb064_alpha_dummy_008))))))).fv) := by
  simpa only [nb064_alpha_dummy_013] using freshVar_not_mem (((Class.cab (nb064_alpha_dummy_007) (syn_wrex (nb064_alpha_dummy_008) (Class.cv (nb064_alpha_dummy_001)) (Wff.classEq (Class.cv (nb064_alpha_dummy_007)) (syn_cphi (Class.cv (nb064_alpha_dummy_008))))))).fv ∪ ((Class.cab (nb064_alpha_dummy_007) (syn_wrex (nb064_alpha_dummy_008) (Class.cv (nb064_alpha_dummy_001)) (Wff.classEq (Class.cv (nb064_alpha_dummy_007)) (syn_cphi (Class.cv (nb064_alpha_dummy_008))))))).fv) 0

theorem nb064_fresh_002 (r : Var) (a : Var) : (nb064_alpha_dummy_038 r a) ∉ (((Class.cab (nb064_alpha_dummy_009 r a) (syn_wrex (nb064_alpha_dummy_010 r a) (Class.cv a) (Wff.classEq (Class.cv (nb064_alpha_dummy_009 r a)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_010 r a))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb064_alpha_dummy_009 r a) (syn_wrex (nb064_alpha_dummy_010 r a) (Class.cv a) (Wff.classEq (Class.cv (nb064_alpha_dummy_009 r a)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_010 r a))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb064_alpha_dummy_038] using freshVar_not_mem (((Class.cab (nb064_alpha_dummy_009 r a) (syn_wrex (nb064_alpha_dummy_010 r a) (Class.cv a) (Wff.classEq (Class.cv (nb064_alpha_dummy_009 r a)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_010 r a))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb064_alpha_dummy_009 r a) (syn_wrex (nb064_alpha_dummy_010 r a) (Class.cv a) (Wff.classEq (Class.cv (nb064_alpha_dummy_009 r a)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_010 r a))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb064_fresh_003 (r : Var) (a : Var) : (nb064_alpha_dummy_014 r a) ∉ (((Class.cab (nb064_alpha_dummy_009 r a) (syn_wrex (nb064_alpha_dummy_010 r a) (Class.cv r) (Wff.classEq (Class.cv (nb064_alpha_dummy_009 r a)) (syn_cphi (Class.cv (nb064_alpha_dummy_010 r a))))))).fv ∪ ((Class.cab (nb064_alpha_dummy_009 r a) (syn_wrex (nb064_alpha_dummy_010 r a) (Class.cv r) (Wff.classEq (Class.cv (nb064_alpha_dummy_009 r a)) (syn_cphi (Class.cv (nb064_alpha_dummy_010 r a))))))).fv) := by
  simpa only [nb064_alpha_dummy_014] using freshVar_not_mem (((Class.cab (nb064_alpha_dummy_009 r a) (syn_wrex (nb064_alpha_dummy_010 r a) (Class.cv r) (Wff.classEq (Class.cv (nb064_alpha_dummy_009 r a)) (syn_cphi (Class.cv (nb064_alpha_dummy_010 r a))))))).fv ∪ ((Class.cab (nb064_alpha_dummy_009 r a) (syn_wrex (nb064_alpha_dummy_010 r a) (Class.cv r) (Wff.classEq (Class.cv (nb064_alpha_dummy_009 r a)) (syn_cphi (Class.cv (nb064_alpha_dummy_010 r a))))))).fv) 0

theorem nb064_fresh_004 : (nb064_alpha_dummy_053) ∉ (((Class.cab (nb064_alpha_dummy_047) (syn_wrex (nb064_alpha_dummy_048) (Class.cv (nb064_alpha_dummy_003)) (Wff.classEq (Class.cv (nb064_alpha_dummy_047)) (syn_cphi (Class.cv (nb064_alpha_dummy_048))))))).fv ∪ ((Class.cab (nb064_alpha_dummy_047) (syn_wrex (nb064_alpha_dummy_048) (Class.cv (nb064_alpha_dummy_003)) (Wff.classEq (Class.cv (nb064_alpha_dummy_047)) (syn_cphi (Class.cv (nb064_alpha_dummy_048))))))).fv) := by
  simpa only [nb064_alpha_dummy_053] using freshVar_not_mem (((Class.cab (nb064_alpha_dummy_047) (syn_wrex (nb064_alpha_dummy_048) (Class.cv (nb064_alpha_dummy_003)) (Wff.classEq (Class.cv (nb064_alpha_dummy_047)) (syn_cphi (Class.cv (nb064_alpha_dummy_048))))))).fv ∪ ((Class.cab (nb064_alpha_dummy_047) (syn_wrex (nb064_alpha_dummy_048) (Class.cv (nb064_alpha_dummy_003)) (Wff.classEq (Class.cv (nb064_alpha_dummy_047)) (syn_cphi (Class.cv (nb064_alpha_dummy_048))))))).fv) 0

theorem nb064_fresh_005 : (nb064_alpha_dummy_077) ∉ (((Class.cab (nb064_alpha_dummy_047) (syn_wrex (nb064_alpha_dummy_048) (Class.cv (nb064_alpha_dummy_004)) (Wff.classEq (Class.cv (nb064_alpha_dummy_047)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_048))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb064_alpha_dummy_047) (syn_wrex (nb064_alpha_dummy_048) (Class.cv (nb064_alpha_dummy_004)) (Wff.classEq (Class.cv (nb064_alpha_dummy_047)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_048))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb064_alpha_dummy_077] using freshVar_not_mem (((Class.cab (nb064_alpha_dummy_047) (syn_wrex (nb064_alpha_dummy_048) (Class.cv (nb064_alpha_dummy_004)) (Wff.classEq (Class.cv (nb064_alpha_dummy_047)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_048))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb064_alpha_dummy_047) (syn_wrex (nb064_alpha_dummy_048) (Class.cv (nb064_alpha_dummy_004)) (Wff.classEq (Class.cv (nb064_alpha_dummy_047)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_048))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb064_fresh_006 (y : Var) (z : Var) : (nb064_alpha_dummy_054 y z) ∉ (((Class.cab (nb064_alpha_dummy_049 y z) (syn_wrex (nb064_alpha_dummy_050 y z) (Class.cv y) (Wff.classEq (Class.cv (nb064_alpha_dummy_049 y z)) (syn_cphi (Class.cv (nb064_alpha_dummy_050 y z))))))).fv ∪ ((Class.cab (nb064_alpha_dummy_049 y z) (syn_wrex (nb064_alpha_dummy_050 y z) (Class.cv y) (Wff.classEq (Class.cv (nb064_alpha_dummy_049 y z)) (syn_cphi (Class.cv (nb064_alpha_dummy_050 y z))))))).fv) := by
  simpa only [nb064_alpha_dummy_054] using freshVar_not_mem (((Class.cab (nb064_alpha_dummy_049 y z) (syn_wrex (nb064_alpha_dummy_050 y z) (Class.cv y) (Wff.classEq (Class.cv (nb064_alpha_dummy_049 y z)) (syn_cphi (Class.cv (nb064_alpha_dummy_050 y z))))))).fv ∪ ((Class.cab (nb064_alpha_dummy_049 y z) (syn_wrex (nb064_alpha_dummy_050 y z) (Class.cv y) (Wff.classEq (Class.cv (nb064_alpha_dummy_049 y z)) (syn_cphi (Class.cv (nb064_alpha_dummy_050 y z))))))).fv) 0

theorem nb064_fresh_007 (y : Var) (z : Var) : (nb064_alpha_dummy_078 y z) ∉ (((Class.cab (nb064_alpha_dummy_049 y z) (syn_wrex (nb064_alpha_dummy_050 y z) (Class.cv z) (Wff.classEq (Class.cv (nb064_alpha_dummy_049 y z)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_050 y z))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb064_alpha_dummy_049 y z) (syn_wrex (nb064_alpha_dummy_050 y z) (Class.cv z) (Wff.classEq (Class.cv (nb064_alpha_dummy_049 y z)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_050 y z))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb064_alpha_dummy_078] using freshVar_not_mem (((Class.cab (nb064_alpha_dummy_049 y z) (syn_wrex (nb064_alpha_dummy_050 y z) (Class.cv z) (Wff.classEq (Class.cv (nb064_alpha_dummy_049 y z)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_050 y z))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb064_alpha_dummy_049 y z) (syn_wrex (nb064_alpha_dummy_050 y z) (Class.cv z) (Wff.classEq (Class.cv (nb064_alpha_dummy_049 y z)) (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_050 y z))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb064_fresh_008 : (nb064_alpha_dummy_007) ∉ (((Class.cv (nb064_alpha_dummy_001))).fv ∪ ((Class.cv (nb064_alpha_dummy_000))).fv) := by
  simpa only [nb064_alpha_dummy_007] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_001))).fv ∪ ((Class.cv (nb064_alpha_dummy_000))).fv) 0

theorem nb064_fresh_009 : (nb064_alpha_dummy_008) ∉ (((Class.cv (nb064_alpha_dummy_001))).fv ∪ ((Class.cv (nb064_alpha_dummy_000))).fv) := by
  simpa only [nb064_alpha_dummy_008] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_001))).fv ∪ ((Class.cv (nb064_alpha_dummy_000))).fv) 1

theorem nb064_distinct_010 : (nb064_alpha_dummy_007) ≠ (nb064_alpha_dummy_008) := by
  simpa only [nb064_alpha_dummy_007, nb064_alpha_dummy_008] using
    (freshVar_injective (((Class.cv (nb064_alpha_dummy_001))).fv ∪ ((Class.cv (nb064_alpha_dummy_000))).fv) (i := 0) (j := 1) (by decide))

theorem nb064_fresh_011 : (nb064_alpha_dummy_045) ∉ (((Class.cv (nb064_alpha_dummy_002))).fv ∪ ((Class.cv (nb064_alpha_dummy_000))).fv) := by
  simpa only [nb064_alpha_dummy_045] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_002))).fv ∪ ((Class.cv (nb064_alpha_dummy_000))).fv) 0

theorem nb064_fresh_012 : (nb064_alpha_dummy_047) ∉ (((Class.cv (nb064_alpha_dummy_003))).fv ∪ ((Class.cv (nb064_alpha_dummy_004))).fv) := by
  simpa only [nb064_alpha_dummy_047] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_003))).fv ∪ ((Class.cv (nb064_alpha_dummy_004))).fv) 0

theorem nb064_fresh_013 : (nb064_alpha_dummy_048) ∉ (((Class.cv (nb064_alpha_dummy_003))).fv ∪ ((Class.cv (nb064_alpha_dummy_004))).fv) := by
  simpa only [nb064_alpha_dummy_048] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_003))).fv ∪ ((Class.cv (nb064_alpha_dummy_004))).fv) 1

theorem nb064_distinct_014 : (nb064_alpha_dummy_047) ≠ (nb064_alpha_dummy_048) := by
  simpa only [nb064_alpha_dummy_047, nb064_alpha_dummy_048] using
    (freshVar_injective (((Class.cv (nb064_alpha_dummy_003))).fv ∪ ((Class.cv (nb064_alpha_dummy_004))).fv) (i := 0) (j := 1) (by decide))

theorem nb064_fresh_015 : (nb064_alpha_dummy_015) ∉ (((Class.cv (nb064_alpha_dummy_008))).fv) := by
  simpa only [nb064_alpha_dummy_015] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_008))).fv) 0

theorem nb064_fresh_016 : (nb064_alpha_dummy_016) ∉ (((Class.cv (nb064_alpha_dummy_008))).fv) := by
  simpa only [nb064_alpha_dummy_016] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_008))).fv) 1

theorem nb064_distinct_017 : (nb064_alpha_dummy_015) ≠ (nb064_alpha_dummy_016) := by
  simpa only [nb064_alpha_dummy_015, nb064_alpha_dummy_016] using
    (freshVar_injective (((Class.cv (nb064_alpha_dummy_008))).fv) (i := 0) (j := 1) (by decide))

theorem nb064_fresh_018 (r : Var) (a : Var) : (nb064_alpha_dummy_017 r a) ∉ (((Class.cv (nb064_alpha_dummy_010 r a))).fv) := by
  simpa only [nb064_alpha_dummy_017] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_010 r a))).fv) 0

theorem nb064_fresh_019 (r : Var) (a : Var) : (nb064_alpha_dummy_018 r a) ∉ (((Class.cv (nb064_alpha_dummy_010 r a))).fv) := by
  simpa only [nb064_alpha_dummy_018] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_010 r a))).fv) 1

theorem nb064_distinct_020 (r : Var) (a : Var) : (nb064_alpha_dummy_017 r a) ≠ (nb064_alpha_dummy_018 r a) := by
  simpa only [nb064_alpha_dummy_017, nb064_alpha_dummy_018] using
    (freshVar_injective (((Class.cv (nb064_alpha_dummy_010 r a))).fv) (i := 0) (j := 1) (by decide))

theorem nb064_fresh_021 : (nb064_alpha_dummy_021) ∉ (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb064_alpha_dummy_021] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) 0

theorem nb064_fresh_022 : (nb064_alpha_dummy_022) ∉ (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb064_alpha_dummy_022] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) 1

theorem nb064_fresh_023 : (nb064_alpha_dummy_023) ∉ (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb064_alpha_dummy_023] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) 2

theorem nb064_distinct_024 : (nb064_alpha_dummy_021) ≠ (nb064_alpha_dummy_022) := by
  simpa only [nb064_alpha_dummy_021, nb064_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb064_distinct_025 : (nb064_alpha_dummy_021) ≠ (nb064_alpha_dummy_023) := by
  simpa only [nb064_alpha_dummy_021, nb064_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb064_distinct_026 : (nb064_alpha_dummy_022) ≠ (nb064_alpha_dummy_023) := by
  simpa only [nb064_alpha_dummy_022, nb064_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb064_fresh_027 (r : Var) (a : Var) : (nb064_alpha_dummy_024 r a) ∉ (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb064_alpha_dummy_024] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) 0

theorem nb064_fresh_028 (r : Var) (a : Var) : (nb064_alpha_dummy_025 r a) ∉ (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb064_alpha_dummy_025] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) 1

theorem nb064_fresh_029 (r : Var) (a : Var) : (nb064_alpha_dummy_026 r a) ∉ (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb064_alpha_dummy_026] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) 2

theorem nb064_distinct_030 (r : Var) (a : Var) : (nb064_alpha_dummy_024 r a) ≠ (nb064_alpha_dummy_025 r a) := by
  simpa only [nb064_alpha_dummy_024, nb064_alpha_dummy_025] using
    (freshVar_injective (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb064_distinct_031 (r : Var) (a : Var) : (nb064_alpha_dummy_024 r a) ≠ (nb064_alpha_dummy_026 r a) := by
  simpa only [nb064_alpha_dummy_024, nb064_alpha_dummy_026] using
    (freshVar_injective (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb064_distinct_032 (r : Var) (a : Var) : (nb064_alpha_dummy_025 r a) ≠ (nb064_alpha_dummy_026 r a) := by
  simpa only [nb064_alpha_dummy_025, nb064_alpha_dummy_026] using
    (freshVar_injective (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb064_fresh_033 : (nb064_alpha_dummy_033) ∉ (((Class.cv (nb064_alpha_dummy_022))).fv ∪ ((Class.cv (nb064_alpha_dummy_022))).fv) := by
  simpa only [nb064_alpha_dummy_033] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_022))).fv ∪ ((Class.cv (nb064_alpha_dummy_022))).fv) 0

theorem nb064_fresh_034 : (nb064_alpha_dummy_029) ∉ (((Class.cv (nb064_alpha_dummy_022))).fv ∪ ((Class.cv (nb064_alpha_dummy_023))).fv) := by
  simpa only [nb064_alpha_dummy_029] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_022))).fv ∪ ((Class.cv (nb064_alpha_dummy_023))).fv) 0

theorem nb064_fresh_035 : (nb064_alpha_dummy_035) ∉ (((Class.cv (nb064_alpha_dummy_023))).fv ∪ ((Class.cv (nb064_alpha_dummy_023))).fv) := by
  simpa only [nb064_alpha_dummy_035] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_023))).fv ∪ ((Class.cv (nb064_alpha_dummy_023))).fv) 0

theorem nb064_fresh_036 (r : Var) (a : Var) : (nb064_alpha_dummy_034 r a) ∉ (((Class.cv (nb064_alpha_dummy_025 r a))).fv ∪ ((Class.cv (nb064_alpha_dummy_025 r a))).fv) := by
  simpa only [nb064_alpha_dummy_034] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_025 r a))).fv ∪ ((Class.cv (nb064_alpha_dummy_025 r a))).fv) 0

theorem nb064_fresh_037 (r : Var) (a : Var) : (nb064_alpha_dummy_030 r a) ∉ (((Class.cv (nb064_alpha_dummy_025 r a))).fv ∪ ((Class.cv (nb064_alpha_dummy_026 r a))).fv) := by
  simpa only [nb064_alpha_dummy_030] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_025 r a))).fv ∪ ((Class.cv (nb064_alpha_dummy_026 r a))).fv) 0

theorem nb064_fresh_038 (r : Var) (a : Var) : (nb064_alpha_dummy_036 r a) ∉ (((Class.cv (nb064_alpha_dummy_026 r a))).fv ∪ ((Class.cv (nb064_alpha_dummy_026 r a))).fv) := by
  simpa only [nb064_alpha_dummy_036] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_026 r a))).fv ∪ ((Class.cv (nb064_alpha_dummy_026 r a))).fv) 0

theorem nb064_fresh_039 : (nb064_alpha_dummy_055) ∉ (((Class.cv (nb064_alpha_dummy_048))).fv) := by
  simpa only [nb064_alpha_dummy_055] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_048))).fv) 0

theorem nb064_fresh_040 : (nb064_alpha_dummy_056) ∉ (((Class.cv (nb064_alpha_dummy_048))).fv) := by
  simpa only [nb064_alpha_dummy_056] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_048))).fv) 1

theorem nb064_distinct_041 : (nb064_alpha_dummy_055) ≠ (nb064_alpha_dummy_056) := by
  simpa only [nb064_alpha_dummy_055, nb064_alpha_dummy_056] using
    (freshVar_injective (((Class.cv (nb064_alpha_dummy_048))).fv) (i := 0) (j := 1) (by decide))

theorem nb064_fresh_042 (y : Var) (z : Var) : (nb064_alpha_dummy_057 y z) ∉ (((Class.cv (nb064_alpha_dummy_050 y z))).fv) := by
  simpa only [nb064_alpha_dummy_057] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_050 y z))).fv) 0

theorem nb064_fresh_043 (y : Var) (z : Var) : (nb064_alpha_dummy_058 y z) ∉ (((Class.cv (nb064_alpha_dummy_050 y z))).fv) := by
  simpa only [nb064_alpha_dummy_058] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_050 y z))).fv) 1

theorem nb064_distinct_044 (y : Var) (z : Var) : (nb064_alpha_dummy_057 y z) ≠ (nb064_alpha_dummy_058 y z) := by
  simpa only [nb064_alpha_dummy_057, nb064_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb064_alpha_dummy_050 y z))).fv) (i := 0) (j := 1) (by decide))

theorem nb064_fresh_045 : (nb064_alpha_dummy_061) ∉ (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb064_alpha_dummy_061] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv) 0

theorem nb064_fresh_046 : (nb064_alpha_dummy_062) ∉ (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb064_alpha_dummy_062] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv) 1

theorem nb064_fresh_047 : (nb064_alpha_dummy_063) ∉ (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb064_alpha_dummy_063] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv) 2

theorem nb064_distinct_048 : (nb064_alpha_dummy_061) ≠ (nb064_alpha_dummy_062) := by
  simpa only [nb064_alpha_dummy_061, nb064_alpha_dummy_062] using
    (freshVar_injective (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb064_distinct_049 : (nb064_alpha_dummy_061) ≠ (nb064_alpha_dummy_063) := by
  simpa only [nb064_alpha_dummy_061, nb064_alpha_dummy_063] using
    (freshVar_injective (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb064_distinct_050 : (nb064_alpha_dummy_062) ≠ (nb064_alpha_dummy_063) := by
  simpa only [nb064_alpha_dummy_062, nb064_alpha_dummy_063] using
    (freshVar_injective (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb064_fresh_051 (y : Var) (z : Var) : (nb064_alpha_dummy_064 y z) ∉ (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb064_alpha_dummy_064] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv) 0

theorem nb064_fresh_052 (y : Var) (z : Var) : (nb064_alpha_dummy_065 y z) ∉ (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb064_alpha_dummy_065] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv) 1

theorem nb064_fresh_053 (y : Var) (z : Var) : (nb064_alpha_dummy_066 y z) ∉ (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb064_alpha_dummy_066] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv) 2

theorem nb064_distinct_054 (y : Var) (z : Var) : (nb064_alpha_dummy_064 y z) ≠ (nb064_alpha_dummy_065 y z) := by
  simpa only [nb064_alpha_dummy_064, nb064_alpha_dummy_065] using
    (freshVar_injective (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb064_distinct_055 (y : Var) (z : Var) : (nb064_alpha_dummy_064 y z) ≠ (nb064_alpha_dummy_066 y z) := by
  simpa only [nb064_alpha_dummy_064, nb064_alpha_dummy_066] using
    (freshVar_injective (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb064_distinct_056 (y : Var) (z : Var) : (nb064_alpha_dummy_065 y z) ≠ (nb064_alpha_dummy_066 y z) := by
  simpa only [nb064_alpha_dummy_065, nb064_alpha_dummy_066] using
    (freshVar_injective (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb064_fresh_057 : (nb064_alpha_dummy_073) ∉ (((Class.cv (nb064_alpha_dummy_062))).fv ∪ ((Class.cv (nb064_alpha_dummy_062))).fv) := by
  simpa only [nb064_alpha_dummy_073] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_062))).fv ∪ ((Class.cv (nb064_alpha_dummy_062))).fv) 0

theorem nb064_fresh_058 : (nb064_alpha_dummy_069) ∉ (((Class.cv (nb064_alpha_dummy_062))).fv ∪ ((Class.cv (nb064_alpha_dummy_063))).fv) := by
  simpa only [nb064_alpha_dummy_069] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_062))).fv ∪ ((Class.cv (nb064_alpha_dummy_063))).fv) 0

theorem nb064_fresh_059 : (nb064_alpha_dummy_075) ∉ (((Class.cv (nb064_alpha_dummy_063))).fv ∪ ((Class.cv (nb064_alpha_dummy_063))).fv) := by
  simpa only [nb064_alpha_dummy_075] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_063))).fv ∪ ((Class.cv (nb064_alpha_dummy_063))).fv) 0

theorem nb064_fresh_060 (y : Var) (z : Var) : (nb064_alpha_dummy_074 y z) ∉ (((Class.cv (nb064_alpha_dummy_065 y z))).fv ∪ ((Class.cv (nb064_alpha_dummy_065 y z))).fv) := by
  simpa only [nb064_alpha_dummy_074] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_065 y z))).fv ∪ ((Class.cv (nb064_alpha_dummy_065 y z))).fv) 0

theorem nb064_fresh_061 (y : Var) (z : Var) : (nb064_alpha_dummy_070 y z) ∉ (((Class.cv (nb064_alpha_dummy_065 y z))).fv ∪ ((Class.cv (nb064_alpha_dummy_066 y z))).fv) := by
  simpa only [nb064_alpha_dummy_070] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_065 y z))).fv ∪ ((Class.cv (nb064_alpha_dummy_066 y z))).fv) 0

theorem nb064_fresh_062 (y : Var) (z : Var) : (nb064_alpha_dummy_076 y z) ∉ (((Class.cv (nb064_alpha_dummy_066 y z))).fv ∪ ((Class.cv (nb064_alpha_dummy_066 y z))).fv) := by
  simpa only [nb064_alpha_dummy_076] using freshVar_not_mem (((Class.cv (nb064_alpha_dummy_066 y z))).fv ∪ ((Class.cv (nb064_alpha_dummy_066 y z))).fv) 0

theorem nb064_fresh_063 (r : Var) (a : Var) : (nb064_alpha_dummy_009 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb064_alpha_dummy_009] using freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0

theorem nb064_fresh_064 (r : Var) (a : Var) : (nb064_alpha_dummy_010 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb064_alpha_dummy_010] using freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1

theorem nb064_distinct_065 (r : Var) (a : Var) : (nb064_alpha_dummy_009 r a) ≠ (nb064_alpha_dummy_010 r a) := by
  simpa only [nb064_alpha_dummy_009, nb064_alpha_dummy_010] using
    (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (i := 0) (j := 1) (by decide))

theorem nb064_fresh_066 (x : Var) (a : Var) : (nb064_alpha_dummy_046 x a) ∉ (((Class.cv x)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb064_alpha_dummy_046] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv a)).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
