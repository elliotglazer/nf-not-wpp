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

noncomputable def nb071_alpha_dummy_000 : Var := (freshVar ((∅ : Finset Var)) 0)

noncomputable def nb071_alpha_dummy_001 : Var := (freshVar (({(nb071_alpha_dummy_000)} : Finset Var) ∪ ((syn_c1c)).fv ∪ ((syn_ctc (syn_cuni (Class.cv (nb071_alpha_dummy_000))))).fv) 0)

noncomputable def nb071_alpha_dummy_002 (x : Var) : Var := (freshVar (({x} : Finset Var) ∪ ((syn_c1c)).fv ∪ ((syn_ctc (syn_cuni (Class.cv x)))).fv) 0)

noncomputable def nb071_alpha_dummy_003 : Var := (freshVar (({(nb071_alpha_dummy_000)} : Finset Var) ∪ ({(nb071_alpha_dummy_001)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_000)) (syn_c1c)) (Wff.classEq (Class.cv (nb071_alpha_dummy_001)) (syn_ctc (syn_cuni (Class.cv (nb071_alpha_dummy_000))))))).fv) 0)

noncomputable def nb071_alpha_dummy_004 (x : Var) : Var := (freshVar (({x} : Finset Var) ∪ ({(nb071_alpha_dummy_002 x)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv x) (syn_c1c)) (Wff.classEq (Class.cv (nb071_alpha_dummy_002 x)) (syn_ctc (syn_cuni (Class.cv x)))))).fv) 0)

noncomputable def nb071_alpha_dummy_005 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_000))).fv ∪ ((Class.cv (nb071_alpha_dummy_001))).fv) 0)

noncomputable def nb071_alpha_dummy_006 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_000))).fv ∪ ((Class.cv (nb071_alpha_dummy_001))).fv) 1)

noncomputable def nb071_alpha_dummy_007 (x : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb071_alpha_dummy_002 x))).fv) 0)

noncomputable def nb071_alpha_dummy_008 (x : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb071_alpha_dummy_002 x))).fv) 1)

noncomputable def nb071_alpha_dummy_009 : Var := (freshVar (((syn_ccompl (Class.cab (nb071_alpha_dummy_005) (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_000)) (Wff.classEq (Class.cv (nb071_alpha_dummy_005)) (syn_cphi (Class.cv (nb071_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl (Class.cab (nb071_alpha_dummy_005) (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_001)) (Wff.classEq (Class.cv (nb071_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_006))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb071_alpha_dummy_010 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb071_alpha_dummy_007 x) (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb071_alpha_dummy_007 x) (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv (nb071_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb071_alpha_dummy_011 : Var := (freshVar (((Class.cab (nb071_alpha_dummy_005) (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_000)) (Wff.classEq (Class.cv (nb071_alpha_dummy_005)) (syn_cphi (Class.cv (nb071_alpha_dummy_006))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_005) (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_000)) (Wff.classEq (Class.cv (nb071_alpha_dummy_005)) (syn_cphi (Class.cv (nb071_alpha_dummy_006))))))).fv) 0)

noncomputable def nb071_alpha_dummy_012 (x : Var) : Var := (freshVar (((Class.cab (nb071_alpha_dummy_007 x) (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_007 x) (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))))))).fv) 0)

noncomputable def nb071_alpha_dummy_013 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_006))).fv) 0)

noncomputable def nb071_alpha_dummy_014 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_006))).fv) 1)

noncomputable def nb071_alpha_dummy_015 (x : Var) : Var := (freshVar (((Class.cv (nb071_alpha_dummy_008 x))).fv) 0)

noncomputable def nb071_alpha_dummy_016 (x : Var) : Var := (freshVar (((Class.cv (nb071_alpha_dummy_008 x))).fv) 1)

noncomputable def nb071_alpha_dummy_017 : Var := (freshVar (((Wff.classMem (Class.cv (nb071_alpha_dummy_013)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb071_alpha_dummy_013)) (syn_c1c))).fv ∪ ((Class.cv (nb071_alpha_dummy_013))).fv) 0)

noncomputable def nb071_alpha_dummy_018 (x : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb071_alpha_dummy_015 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb071_alpha_dummy_015 x)) (syn_c1c))).fv ∪ ((Class.cv (nb071_alpha_dummy_015 x))).fv) 0)

noncomputable def nb071_alpha_dummy_019 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb071_alpha_dummy_020 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb071_alpha_dummy_021 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb071_alpha_dummy_022 (x : Var) : Var := (freshVar (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb071_alpha_dummy_023 (x : Var) : Var := (freshVar (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb071_alpha_dummy_024 (x : Var) : Var := (freshVar (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb071_alpha_dummy_025 : Var := (freshVar (((syn_cnin (Class.cv (nb071_alpha_dummy_020)) (Class.cv (nb071_alpha_dummy_021)))).fv ∪ ((syn_cnin (Class.cv (nb071_alpha_dummy_020)) (Class.cv (nb071_alpha_dummy_021)))).fv) 0)

noncomputable def nb071_alpha_dummy_026 (x : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb071_alpha_dummy_023 x)) (Class.cv (nb071_alpha_dummy_024 x)))).fv ∪ ((syn_cnin (Class.cv (nb071_alpha_dummy_023 x)) (Class.cv (nb071_alpha_dummy_024 x)))).fv) 0)

noncomputable def nb071_alpha_dummy_027 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_020))).fv ∪ ((Class.cv (nb071_alpha_dummy_021))).fv) 0)

noncomputable def nb071_alpha_dummy_028 (x : Var) : Var := (freshVar (((Class.cv (nb071_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_024 x))).fv) 0)

noncomputable def nb071_alpha_dummy_029 : Var := (freshVar (((syn_ccompl (Class.cv (nb071_alpha_dummy_020)))).fv ∪ ((syn_ccompl (Class.cv (nb071_alpha_dummy_021)))).fv) 0)

noncomputable def nb071_alpha_dummy_030 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb071_alpha_dummy_023 x)))).fv ∪ ((syn_ccompl (Class.cv (nb071_alpha_dummy_024 x)))).fv) 0)

noncomputable def nb071_alpha_dummy_031 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_020))).fv ∪ ((Class.cv (nb071_alpha_dummy_020))).fv) 0)

noncomputable def nb071_alpha_dummy_032 (x : Var) : Var := (freshVar (((Class.cv (nb071_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_023 x))).fv) 0)

noncomputable def nb071_alpha_dummy_033 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_021))).fv ∪ ((Class.cv (nb071_alpha_dummy_021))).fv) 0)

noncomputable def nb071_alpha_dummy_034 (x : Var) : Var := (freshVar (((Class.cv (nb071_alpha_dummy_024 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_024 x))).fv) 0)

noncomputable def nb071_alpha_dummy_035 : Var := (freshVar (((Class.cab (nb071_alpha_dummy_005) (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_001)) (Wff.classEq (Class.cv (nb071_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_005) (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_001)) (Wff.classEq (Class.cv (nb071_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb071_alpha_dummy_036 (x : Var) : Var := (freshVar (((Class.cab (nb071_alpha_dummy_007 x) (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv (nb071_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_007 x) (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv (nb071_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb071_alpha_dummy_037 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb071_alpha_dummy_006))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb071_alpha_dummy_038 (x : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb071_alpha_dummy_039 : Var := (freshVar (((syn_cphi (Class.cv (nb071_alpha_dummy_006)))).fv ∪ ((syn_cphi (Class.cv (nb071_alpha_dummy_006)))).fv) 0)

noncomputable def nb071_alpha_dummy_040 (x : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))).fv ∪ ((syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))).fv) 0)

noncomputable def nb071_alpha_dummy_041 : Var := (freshVar (((syn_cuni (Class.cv (nb071_alpha_dummy_000)))).fv) 0)

noncomputable def nb071_alpha_dummy_042 : Var := (freshVar (((syn_cuni (Class.cv (nb071_alpha_dummy_000)))).fv) 1)

noncomputable def nb071_alpha_dummy_043 (x : Var) : Var := (freshVar (((syn_cuni (Class.cv x))).fv) 0)

noncomputable def nb071_alpha_dummy_044 (x : Var) : Var := (freshVar (((syn_cuni (Class.cv x))).fv) 1)

noncomputable def nb071_alpha_dummy_045 : Var := (freshVar (({(nb071_alpha_dummy_041)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_041)) (syn_cncs)) (syn_wrex (nb071_alpha_dummy_042) (syn_cuni (Class.cv (nb071_alpha_dummy_000))) (Wff.classEq (Class.cv (nb071_alpha_dummy_041)) (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_042)))))))).fv) 0)

noncomputable def nb071_alpha_dummy_046 (x : Var) : Var := (freshVar (({(nb071_alpha_dummy_043 x)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_043 x)) (syn_cncs)) (syn_wrex (nb071_alpha_dummy_044 x) (syn_cuni (Class.cv x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_043 x)) (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x)))))))).fv) 0)

noncomputable def nb071_alpha_dummy_047 : Var := (freshVar (((Class.cab (nb071_alpha_dummy_045) (Wff.classEq (Class.cab (nb071_alpha_dummy_041) (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_041)) (syn_cncs)) (syn_wrex (nb071_alpha_dummy_042) (syn_cuni (Class.cv (nb071_alpha_dummy_000))) (Wff.classEq (Class.cv (nb071_alpha_dummy_041)) (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_042)))))))) (syn_csn (Class.cv (nb071_alpha_dummy_045)))))).fv) 0)

noncomputable def nb071_alpha_dummy_048 : Var := (freshVar (((Class.cab (nb071_alpha_dummy_045) (Wff.classEq (Class.cab (nb071_alpha_dummy_041) (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_041)) (syn_cncs)) (syn_wrex (nb071_alpha_dummy_042) (syn_cuni (Class.cv (nb071_alpha_dummy_000))) (Wff.classEq (Class.cv (nb071_alpha_dummy_041)) (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_042)))))))) (syn_csn (Class.cv (nb071_alpha_dummy_045)))))).fv) 1)

noncomputable def nb071_alpha_dummy_049 (x : Var) : Var := (freshVar (((Class.cab (nb071_alpha_dummy_046 x) (Wff.classEq (Class.cab (nb071_alpha_dummy_043 x) (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_043 x)) (syn_cncs)) (syn_wrex (nb071_alpha_dummy_044 x) (syn_cuni (Class.cv x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_043 x)) (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x)))))))) (syn_csn (Class.cv (nb071_alpha_dummy_046 x)))))).fv) 0)

noncomputable def nb071_alpha_dummy_050 (x : Var) : Var := (freshVar (((Class.cab (nb071_alpha_dummy_046 x) (Wff.classEq (Class.cab (nb071_alpha_dummy_043 x) (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_043 x)) (syn_cncs)) (syn_wrex (nb071_alpha_dummy_044 x) (syn_cuni (Class.cv x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_043 x)) (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x)))))))) (syn_csn (Class.cv (nb071_alpha_dummy_046 x)))))).fv) 1)

noncomputable def nb071_alpha_dummy_051 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_000))).fv) 0)

noncomputable def nb071_alpha_dummy_052 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_000))).fv) 1)

noncomputable def nb071_alpha_dummy_053 (x : Var) : Var := (freshVar (((Class.cv x)).fv) 0)

noncomputable def nb071_alpha_dummy_054 (x : Var) : Var := (freshVar (((Class.cv x)).fv) 1)

noncomputable def nb071_alpha_dummy_055 : Var := (freshVar (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb071_alpha_dummy_042))))).fv) 0)

noncomputable def nb071_alpha_dummy_056 : Var := (freshVar (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb071_alpha_dummy_042))))).fv) 1)

noncomputable def nb071_alpha_dummy_057 (x : Var) : Var := (freshVar (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x))))).fv) 0)

noncomputable def nb071_alpha_dummy_058 (x : Var) : Var := (freshVar (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x))))).fv) 1)

noncomputable def nb071_alpha_dummy_059 : Var := (freshVar (((syn_cpw1 (Class.cv (nb071_alpha_dummy_042)))).fv) 0)

noncomputable def nb071_alpha_dummy_060 (x : Var) : Var := (freshVar (((syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x)))).fv) 0)

noncomputable def nb071_alpha_dummy_061 : Var := (freshVar (((syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_042))) (syn_c1c))).fv ∪ ((syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_042))) (syn_c1c))).fv) 0)

noncomputable def nb071_alpha_dummy_062 (x : Var) : Var := (freshVar (((syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_044 x))) (syn_c1c))).fv ∪ ((syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_044 x))) (syn_c1c))).fv) 0)

noncomputable def nb071_alpha_dummy_063 : Var := (freshVar (((syn_cpw (Class.cv (nb071_alpha_dummy_042)))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb071_alpha_dummy_064 (x : Var) : Var := (freshVar (((syn_cpw (Class.cv (nb071_alpha_dummy_044 x)))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb071_alpha_dummy_065 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_042))).fv) 0)

noncomputable def nb071_alpha_dummy_066 (x : Var) : Var := (freshVar (((Class.cv (nb071_alpha_dummy_044 x))).fv) 0)

noncomputable def nb071_alpha_dummy_067 : Var := (freshVar (((syn_cnin (Class.cv (nb071_alpha_dummy_065)) (Class.cv (nb071_alpha_dummy_042)))).fv ∪ ((syn_cnin (Class.cv (nb071_alpha_dummy_065)) (Class.cv (nb071_alpha_dummy_042)))).fv) 0)

noncomputable def nb071_alpha_dummy_068 (x : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb071_alpha_dummy_066 x)) (Class.cv (nb071_alpha_dummy_044 x)))).fv ∪ ((syn_cnin (Class.cv (nb071_alpha_dummy_066 x)) (Class.cv (nb071_alpha_dummy_044 x)))).fv) 0)

noncomputable def nb071_alpha_dummy_069 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_065))).fv ∪ ((Class.cv (nb071_alpha_dummy_042))).fv) 0)

noncomputable def nb071_alpha_dummy_070 (x : Var) : Var := (freshVar (((Class.cv (nb071_alpha_dummy_066 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_044 x))).fv) 0)

noncomputable def nb071_alpha_dummy_071 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_056))).fv ∪ ((Class.cv (nb071_alpha_dummy_055))).fv) 0)

noncomputable def nb071_alpha_dummy_072 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_056))).fv ∪ ((Class.cv (nb071_alpha_dummy_055))).fv) 1)

noncomputable def nb071_alpha_dummy_073 (x : Var) : Var := (freshVar (((Class.cv (nb071_alpha_dummy_058 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_057 x))).fv) 0)

noncomputable def nb071_alpha_dummy_074 (x : Var) : Var := (freshVar (((Class.cv (nb071_alpha_dummy_058 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_057 x))).fv) 1)

noncomputable def nb071_alpha_dummy_075 : Var := (freshVar (((syn_ccompl (Class.cab (nb071_alpha_dummy_071) (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_056)) (Wff.classEq (Class.cv (nb071_alpha_dummy_071)) (syn_cphi (Class.cv (nb071_alpha_dummy_072)))))))).fv ∪ ((syn_ccompl (Class.cab (nb071_alpha_dummy_071) (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055)) (Wff.classEq (Class.cv (nb071_alpha_dummy_071)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb071_alpha_dummy_076 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb071_alpha_dummy_073 x) (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_058 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x)) (syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb071_alpha_dummy_073 x) (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb071_alpha_dummy_077 : Var := (freshVar (((Class.cab (nb071_alpha_dummy_071) (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_056)) (Wff.classEq (Class.cv (nb071_alpha_dummy_071)) (syn_cphi (Class.cv (nb071_alpha_dummy_072))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_071) (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_056)) (Wff.classEq (Class.cv (nb071_alpha_dummy_071)) (syn_cphi (Class.cv (nb071_alpha_dummy_072))))))).fv) 0)

noncomputable def nb071_alpha_dummy_078 (x : Var) : Var := (freshVar (((Class.cab (nb071_alpha_dummy_073 x) (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_058 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x)) (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_073 x) (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_058 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x)) (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))))))).fv) 0)

noncomputable def nb071_alpha_dummy_079 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_072))).fv) 0)

noncomputable def nb071_alpha_dummy_080 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_072))).fv) 1)

noncomputable def nb071_alpha_dummy_081 (x : Var) : Var := (freshVar (((Class.cv (nb071_alpha_dummy_074 x))).fv) 0)

noncomputable def nb071_alpha_dummy_082 (x : Var) : Var := (freshVar (((Class.cv (nb071_alpha_dummy_074 x))).fv) 1)

noncomputable def nb071_alpha_dummy_083 : Var := (freshVar (((Wff.classMem (Class.cv (nb071_alpha_dummy_079)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb071_alpha_dummy_079)) (syn_c1c))).fv ∪ ((Class.cv (nb071_alpha_dummy_079))).fv) 0)

noncomputable def nb071_alpha_dummy_084 (x : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb071_alpha_dummy_081 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb071_alpha_dummy_081 x)) (syn_c1c))).fv ∪ ((Class.cv (nb071_alpha_dummy_081 x))).fv) 0)

noncomputable def nb071_alpha_dummy_085 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb071_alpha_dummy_086 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb071_alpha_dummy_087 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb071_alpha_dummy_088 (x : Var) : Var := (freshVar (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb071_alpha_dummy_089 (x : Var) : Var := (freshVar (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb071_alpha_dummy_090 (x : Var) : Var := (freshVar (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb071_alpha_dummy_091 : Var := (freshVar (((syn_cnin (Class.cv (nb071_alpha_dummy_086)) (Class.cv (nb071_alpha_dummy_087)))).fv ∪ ((syn_cnin (Class.cv (nb071_alpha_dummy_086)) (Class.cv (nb071_alpha_dummy_087)))).fv) 0)

noncomputable def nb071_alpha_dummy_092 (x : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb071_alpha_dummy_089 x)) (Class.cv (nb071_alpha_dummy_090 x)))).fv ∪ ((syn_cnin (Class.cv (nb071_alpha_dummy_089 x)) (Class.cv (nb071_alpha_dummy_090 x)))).fv) 0)

noncomputable def nb071_alpha_dummy_093 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_086))).fv ∪ ((Class.cv (nb071_alpha_dummy_087))).fv) 0)

noncomputable def nb071_alpha_dummy_094 (x : Var) : Var := (freshVar (((Class.cv (nb071_alpha_dummy_089 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_090 x))).fv) 0)

noncomputable def nb071_alpha_dummy_095 : Var := (freshVar (((syn_ccompl (Class.cv (nb071_alpha_dummy_086)))).fv ∪ ((syn_ccompl (Class.cv (nb071_alpha_dummy_087)))).fv) 0)

noncomputable def nb071_alpha_dummy_096 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb071_alpha_dummy_089 x)))).fv ∪ ((syn_ccompl (Class.cv (nb071_alpha_dummy_090 x)))).fv) 0)

noncomputable def nb071_alpha_dummy_097 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_086))).fv ∪ ((Class.cv (nb071_alpha_dummy_086))).fv) 0)

noncomputable def nb071_alpha_dummy_098 (x : Var) : Var := (freshVar (((Class.cv (nb071_alpha_dummy_089 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_089 x))).fv) 0)

noncomputable def nb071_alpha_dummy_099 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_087))).fv ∪ ((Class.cv (nb071_alpha_dummy_087))).fv) 0)

noncomputable def nb071_alpha_dummy_100 (x : Var) : Var := (freshVar (((Class.cv (nb071_alpha_dummy_090 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_090 x))).fv) 0)

noncomputable def nb071_alpha_dummy_101 : Var := (freshVar (((Class.cab (nb071_alpha_dummy_071) (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055)) (Wff.classEq (Class.cv (nb071_alpha_dummy_071)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_071) (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055)) (Wff.classEq (Class.cv (nb071_alpha_dummy_071)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb071_alpha_dummy_102 (x : Var) : Var := (freshVar (((Class.cab (nb071_alpha_dummy_073 x) (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_073 x) (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb071_alpha_dummy_103 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb071_alpha_dummy_072))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb071_alpha_dummy_104 (x : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb071_alpha_dummy_105 : Var := (freshVar (((syn_cphi (Class.cv (nb071_alpha_dummy_072)))).fv ∪ ((syn_cphi (Class.cv (nb071_alpha_dummy_072)))).fv) 0)

noncomputable def nb071_alpha_dummy_106 (x : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))).fv ∪ ((syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))).fv) 0)

noncomputable def nb071_alpha_dummy_107 : Var := (freshVar (((Class.cv (nb071_alpha_dummy_045))).fv) 0)

noncomputable def nb071_alpha_dummy_108 (x : Var) : Var := (freshVar (((Class.cv (nb071_alpha_dummy_046 x))).fv) 0)

theorem nb071_fresh_000 : (nb071_alpha_dummy_011) ∉ (((Class.cab (nb071_alpha_dummy_005) (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_000)) (Wff.classEq (Class.cv (nb071_alpha_dummy_005)) (syn_cphi (Class.cv (nb071_alpha_dummy_006))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_005) (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_000)) (Wff.classEq (Class.cv (nb071_alpha_dummy_005)) (syn_cphi (Class.cv (nb071_alpha_dummy_006))))))).fv) := by
  simpa only [nb071_alpha_dummy_011] using freshVar_not_mem (((Class.cab (nb071_alpha_dummy_005) (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_000)) (Wff.classEq (Class.cv (nb071_alpha_dummy_005)) (syn_cphi (Class.cv (nb071_alpha_dummy_006))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_005) (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_000)) (Wff.classEq (Class.cv (nb071_alpha_dummy_005)) (syn_cphi (Class.cv (nb071_alpha_dummy_006))))))).fv) 0

theorem nb071_fresh_001 : (nb071_alpha_dummy_035) ∉ (((Class.cab (nb071_alpha_dummy_005) (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_001)) (Wff.classEq (Class.cv (nb071_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_005) (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_001)) (Wff.classEq (Class.cv (nb071_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb071_alpha_dummy_035] using freshVar_not_mem (((Class.cab (nb071_alpha_dummy_005) (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_001)) (Wff.classEq (Class.cv (nb071_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_005) (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_001)) (Wff.classEq (Class.cv (nb071_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb071_fresh_002 (x : Var) : (nb071_alpha_dummy_036 x) ∉ (((Class.cab (nb071_alpha_dummy_007 x) (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv (nb071_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_007 x) (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv (nb071_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb071_alpha_dummy_036] using freshVar_not_mem (((Class.cab (nb071_alpha_dummy_007 x) (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv (nb071_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_007 x) (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv (nb071_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb071_fresh_003 (x : Var) : (nb071_alpha_dummy_012 x) ∉ (((Class.cab (nb071_alpha_dummy_007 x) (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_007 x) (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))))))).fv) := by
  simpa only [nb071_alpha_dummy_012] using freshVar_not_mem (((Class.cab (nb071_alpha_dummy_007 x) (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_007 x) (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))))))).fv) 0

theorem nb071_fresh_004 : (nb071_alpha_dummy_047) ∉ (((Class.cab (nb071_alpha_dummy_045) (Wff.classEq (Class.cab (nb071_alpha_dummy_041) (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_041)) (syn_cncs)) (syn_wrex (nb071_alpha_dummy_042) (syn_cuni (Class.cv (nb071_alpha_dummy_000))) (Wff.classEq (Class.cv (nb071_alpha_dummy_041)) (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_042)))))))) (syn_csn (Class.cv (nb071_alpha_dummy_045)))))).fv) := by
  simpa only [nb071_alpha_dummy_047] using freshVar_not_mem (((Class.cab (nb071_alpha_dummy_045) (Wff.classEq (Class.cab (nb071_alpha_dummy_041) (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_041)) (syn_cncs)) (syn_wrex (nb071_alpha_dummy_042) (syn_cuni (Class.cv (nb071_alpha_dummy_000))) (Wff.classEq (Class.cv (nb071_alpha_dummy_041)) (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_042)))))))) (syn_csn (Class.cv (nb071_alpha_dummy_045)))))).fv) 0

theorem nb071_fresh_005 : (nb071_alpha_dummy_048) ∉ (((Class.cab (nb071_alpha_dummy_045) (Wff.classEq (Class.cab (nb071_alpha_dummy_041) (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_041)) (syn_cncs)) (syn_wrex (nb071_alpha_dummy_042) (syn_cuni (Class.cv (nb071_alpha_dummy_000))) (Wff.classEq (Class.cv (nb071_alpha_dummy_041)) (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_042)))))))) (syn_csn (Class.cv (nb071_alpha_dummy_045)))))).fv) := by
  simpa only [nb071_alpha_dummy_048] using freshVar_not_mem (((Class.cab (nb071_alpha_dummy_045) (Wff.classEq (Class.cab (nb071_alpha_dummy_041) (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_041)) (syn_cncs)) (syn_wrex (nb071_alpha_dummy_042) (syn_cuni (Class.cv (nb071_alpha_dummy_000))) (Wff.classEq (Class.cv (nb071_alpha_dummy_041)) (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_042)))))))) (syn_csn (Class.cv (nb071_alpha_dummy_045)))))).fv) 1

theorem nb071_distinct_006 : (nb071_alpha_dummy_047) ≠ (nb071_alpha_dummy_048) := by
  simpa only [nb071_alpha_dummy_047, nb071_alpha_dummy_048] using
    (freshVar_injective (((Class.cab (nb071_alpha_dummy_045) (Wff.classEq (Class.cab (nb071_alpha_dummy_041) (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_041)) (syn_cncs)) (syn_wrex (nb071_alpha_dummy_042) (syn_cuni (Class.cv (nb071_alpha_dummy_000))) (Wff.classEq (Class.cv (nb071_alpha_dummy_041)) (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_042)))))))) (syn_csn (Class.cv (nb071_alpha_dummy_045)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb071_fresh_007 (x : Var) : (nb071_alpha_dummy_049 x) ∉ (((Class.cab (nb071_alpha_dummy_046 x) (Wff.classEq (Class.cab (nb071_alpha_dummy_043 x) (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_043 x)) (syn_cncs)) (syn_wrex (nb071_alpha_dummy_044 x) (syn_cuni (Class.cv x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_043 x)) (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x)))))))) (syn_csn (Class.cv (nb071_alpha_dummy_046 x)))))).fv) := by
  simpa only [nb071_alpha_dummy_049] using freshVar_not_mem (((Class.cab (nb071_alpha_dummy_046 x) (Wff.classEq (Class.cab (nb071_alpha_dummy_043 x) (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_043 x)) (syn_cncs)) (syn_wrex (nb071_alpha_dummy_044 x) (syn_cuni (Class.cv x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_043 x)) (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x)))))))) (syn_csn (Class.cv (nb071_alpha_dummy_046 x)))))).fv) 0

theorem nb071_fresh_008 (x : Var) : (nb071_alpha_dummy_050 x) ∉ (((Class.cab (nb071_alpha_dummy_046 x) (Wff.classEq (Class.cab (nb071_alpha_dummy_043 x) (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_043 x)) (syn_cncs)) (syn_wrex (nb071_alpha_dummy_044 x) (syn_cuni (Class.cv x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_043 x)) (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x)))))))) (syn_csn (Class.cv (nb071_alpha_dummy_046 x)))))).fv) := by
  simpa only [nb071_alpha_dummy_050] using freshVar_not_mem (((Class.cab (nb071_alpha_dummy_046 x) (Wff.classEq (Class.cab (nb071_alpha_dummy_043 x) (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_043 x)) (syn_cncs)) (syn_wrex (nb071_alpha_dummy_044 x) (syn_cuni (Class.cv x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_043 x)) (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x)))))))) (syn_csn (Class.cv (nb071_alpha_dummy_046 x)))))).fv) 1

theorem nb071_distinct_009 (x : Var) : (nb071_alpha_dummy_049 x) ≠ (nb071_alpha_dummy_050 x) := by
  simpa only [nb071_alpha_dummy_049, nb071_alpha_dummy_050] using
    (freshVar_injective (((Class.cab (nb071_alpha_dummy_046 x) (Wff.classEq (Class.cab (nb071_alpha_dummy_043 x) (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_043 x)) (syn_cncs)) (syn_wrex (nb071_alpha_dummy_044 x) (syn_cuni (Class.cv x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_043 x)) (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x)))))))) (syn_csn (Class.cv (nb071_alpha_dummy_046 x)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb071_fresh_010 : (nb071_alpha_dummy_101) ∉ (((Class.cab (nb071_alpha_dummy_071) (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055)) (Wff.classEq (Class.cv (nb071_alpha_dummy_071)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_071) (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055)) (Wff.classEq (Class.cv (nb071_alpha_dummy_071)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb071_alpha_dummy_101] using freshVar_not_mem (((Class.cab (nb071_alpha_dummy_071) (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055)) (Wff.classEq (Class.cv (nb071_alpha_dummy_071)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_071) (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055)) (Wff.classEq (Class.cv (nb071_alpha_dummy_071)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb071_fresh_011 : (nb071_alpha_dummy_077) ∉ (((Class.cab (nb071_alpha_dummy_071) (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_056)) (Wff.classEq (Class.cv (nb071_alpha_dummy_071)) (syn_cphi (Class.cv (nb071_alpha_dummy_072))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_071) (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_056)) (Wff.classEq (Class.cv (nb071_alpha_dummy_071)) (syn_cphi (Class.cv (nb071_alpha_dummy_072))))))).fv) := by
  simpa only [nb071_alpha_dummy_077] using freshVar_not_mem (((Class.cab (nb071_alpha_dummy_071) (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_056)) (Wff.classEq (Class.cv (nb071_alpha_dummy_071)) (syn_cphi (Class.cv (nb071_alpha_dummy_072))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_071) (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_056)) (Wff.classEq (Class.cv (nb071_alpha_dummy_071)) (syn_cphi (Class.cv (nb071_alpha_dummy_072))))))).fv) 0

theorem nb071_fresh_012 (x : Var) : (nb071_alpha_dummy_102 x) ∉ (((Class.cab (nb071_alpha_dummy_073 x) (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_073 x) (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb071_alpha_dummy_102] using freshVar_not_mem (((Class.cab (nb071_alpha_dummy_073 x) (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_073 x) (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb071_fresh_013 (x : Var) : (nb071_alpha_dummy_078 x) ∉ (((Class.cab (nb071_alpha_dummy_073 x) (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_058 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x)) (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_073 x) (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_058 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x)) (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))))))).fv) := by
  simpa only [nb071_alpha_dummy_078] using freshVar_not_mem (((Class.cab (nb071_alpha_dummy_073 x) (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_058 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x)) (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_073 x) (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_058 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x)) (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))))))).fv) 0

theorem nb071_fresh_014 : (nb071_alpha_dummy_051) ∉ (((Class.cv (nb071_alpha_dummy_000))).fv) := by
  simpa only [nb071_alpha_dummy_051] using freshVar_not_mem (((Class.cv (nb071_alpha_dummy_000))).fv) 0

theorem nb071_fresh_015 : (nb071_alpha_dummy_052) ∉ (((Class.cv (nb071_alpha_dummy_000))).fv) := by
  simpa only [nb071_alpha_dummy_052] using freshVar_not_mem (((Class.cv (nb071_alpha_dummy_000))).fv) 1

theorem nb071_distinct_016 : (nb071_alpha_dummy_051) ≠ (nb071_alpha_dummy_052) := by
  simpa only [nb071_alpha_dummy_051, nb071_alpha_dummy_052] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_000))).fv) (i := 0) (j := 1) (by decide))

theorem nb071_fresh_017 : (nb071_alpha_dummy_005) ∉ (((Class.cv (nb071_alpha_dummy_000))).fv ∪ ((Class.cv (nb071_alpha_dummy_001))).fv) := by
  simpa only [nb071_alpha_dummy_005] using freshVar_not_mem (((Class.cv (nb071_alpha_dummy_000))).fv ∪ ((Class.cv (nb071_alpha_dummy_001))).fv) 0

theorem nb071_fresh_018 : (nb071_alpha_dummy_006) ∉ (((Class.cv (nb071_alpha_dummy_000))).fv ∪ ((Class.cv (nb071_alpha_dummy_001))).fv) := by
  simpa only [nb071_alpha_dummy_006] using freshVar_not_mem (((Class.cv (nb071_alpha_dummy_000))).fv ∪ ((Class.cv (nb071_alpha_dummy_001))).fv) 1

theorem nb071_distinct_019 : (nb071_alpha_dummy_005) ≠ (nb071_alpha_dummy_006) := by
  simpa only [nb071_alpha_dummy_005, nb071_alpha_dummy_006] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_000))).fv ∪ ((Class.cv (nb071_alpha_dummy_001))).fv) (i := 0) (j := 1) (by decide))

theorem nb071_fresh_020 : (nb071_alpha_dummy_013) ∉ (((Class.cv (nb071_alpha_dummy_006))).fv) := by
  simpa only [nb071_alpha_dummy_013] using freshVar_not_mem (((Class.cv (nb071_alpha_dummy_006))).fv) 0

theorem nb071_fresh_021 : (nb071_alpha_dummy_014) ∉ (((Class.cv (nb071_alpha_dummy_006))).fv) := by
  simpa only [nb071_alpha_dummy_014] using freshVar_not_mem (((Class.cv (nb071_alpha_dummy_006))).fv) 1

theorem nb071_distinct_022 : (nb071_alpha_dummy_013) ≠ (nb071_alpha_dummy_014) := by
  simpa only [nb071_alpha_dummy_013, nb071_alpha_dummy_014] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_006))).fv) (i := 0) (j := 1) (by decide))

theorem nb071_fresh_023 (x : Var) : (nb071_alpha_dummy_015 x) ∉ (((Class.cv (nb071_alpha_dummy_008 x))).fv) := by
  simpa only [nb071_alpha_dummy_015] using freshVar_not_mem (((Class.cv (nb071_alpha_dummy_008 x))).fv) 0

theorem nb071_fresh_024 (x : Var) : (nb071_alpha_dummy_016 x) ∉ (((Class.cv (nb071_alpha_dummy_008 x))).fv) := by
  simpa only [nb071_alpha_dummy_016] using freshVar_not_mem (((Class.cv (nb071_alpha_dummy_008 x))).fv) 1

theorem nb071_distinct_025 (x : Var) : (nb071_alpha_dummy_015 x) ≠ (nb071_alpha_dummy_016 x) := by
  simpa only [nb071_alpha_dummy_015, nb071_alpha_dummy_016] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_008 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb071_fresh_026 : (nb071_alpha_dummy_019) ∉ (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb071_alpha_dummy_019] using freshVar_not_mem (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 0

theorem nb071_fresh_027 : (nb071_alpha_dummy_020) ∉ (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb071_alpha_dummy_020] using freshVar_not_mem (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 1

theorem nb071_fresh_028 : (nb071_alpha_dummy_021) ∉ (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb071_alpha_dummy_021] using freshVar_not_mem (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 2

theorem nb071_distinct_029 : (nb071_alpha_dummy_019) ≠ (nb071_alpha_dummy_020) := by
  simpa only [nb071_alpha_dummy_019, nb071_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb071_distinct_030 : (nb071_alpha_dummy_019) ≠ (nb071_alpha_dummy_021) := by
  simpa only [nb071_alpha_dummy_019, nb071_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb071_distinct_031 : (nb071_alpha_dummy_020) ≠ (nb071_alpha_dummy_021) := by
  simpa only [nb071_alpha_dummy_020, nb071_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb071_fresh_032 (x : Var) : (nb071_alpha_dummy_022 x) ∉ (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb071_alpha_dummy_022] using freshVar_not_mem (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb071_fresh_033 (x : Var) : (nb071_alpha_dummy_023 x) ∉ (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb071_alpha_dummy_023] using freshVar_not_mem (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb071_fresh_034 (x : Var) : (nb071_alpha_dummy_024 x) ∉ (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb071_alpha_dummy_024] using freshVar_not_mem (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb071_distinct_035 (x : Var) : (nb071_alpha_dummy_022 x) ≠ (nb071_alpha_dummy_023 x) := by
  simpa only [nb071_alpha_dummy_022, nb071_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb071_distinct_036 (x : Var) : (nb071_alpha_dummy_022 x) ≠ (nb071_alpha_dummy_024 x) := by
  simpa only [nb071_alpha_dummy_022, nb071_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb071_distinct_037 (x : Var) : (nb071_alpha_dummy_023 x) ≠ (nb071_alpha_dummy_024 x) := by
  simpa only [nb071_alpha_dummy_023, nb071_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb071_fresh_038 : (nb071_alpha_dummy_031) ∉ (((Class.cv (nb071_alpha_dummy_020))).fv ∪ ((Class.cv (nb071_alpha_dummy_020))).fv) := by
  simpa only [nb071_alpha_dummy_031] using freshVar_not_mem (((Class.cv (nb071_alpha_dummy_020))).fv ∪ ((Class.cv (nb071_alpha_dummy_020))).fv) 0

theorem nb071_fresh_039 : (nb071_alpha_dummy_027) ∉ (((Class.cv (nb071_alpha_dummy_020))).fv ∪ ((Class.cv (nb071_alpha_dummy_021))).fv) := by
  simpa only [nb071_alpha_dummy_027] using freshVar_not_mem (((Class.cv (nb071_alpha_dummy_020))).fv ∪ ((Class.cv (nb071_alpha_dummy_021))).fv) 0

theorem nb071_fresh_040 : (nb071_alpha_dummy_033) ∉ (((Class.cv (nb071_alpha_dummy_021))).fv ∪ ((Class.cv (nb071_alpha_dummy_021))).fv) := by
  simpa only [nb071_alpha_dummy_033] using freshVar_not_mem (((Class.cv (nb071_alpha_dummy_021))).fv ∪ ((Class.cv (nb071_alpha_dummy_021))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
