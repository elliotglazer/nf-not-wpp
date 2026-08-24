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

noncomputable def nb061_alpha_dummy_000 : Var := (freshVar ((∅ : Finset Var)) 0)

noncomputable def nb061_alpha_dummy_001 : Var := (freshVar ((∅ : Finset Var)) 1)

noncomputable def nb061_alpha_dummy_002 : Var := (freshVar ((∅ : Finset Var)) 2)

noncomputable def nb061_alpha_dummy_003 : Var := (freshVar (({(nb061_alpha_dummy_001)} : Finset Var) ∪ ({(nb061_alpha_dummy_000)} : Finset Var) ∪ ((syn_wral (nb061_alpha_dummy_002) (Class.cv (nb061_alpha_dummy_000)) (syn_wbr (Class.cv (nb061_alpha_dummy_002)) (Class.cv (nb061_alpha_dummy_001)) (Class.cv (nb061_alpha_dummy_002))))).fv) 0)

noncomputable def nb061_alpha_dummy_004 (x : Var) (r : Var) (a : Var) : Var := (freshVar (({r} : Finset Var) ∪ ({a} : Finset Var) ∪ ((syn_wral x (Class.cv a) (syn_wbr (Class.cv x) (Class.cv r) (Class.cv x)))).fv) 0)

noncomputable def nb061_alpha_dummy_005 : Var := (freshVar (((Class.cv (nb061_alpha_dummy_001))).fv ∪ ((Class.cv (nb061_alpha_dummy_000))).fv) 0)

noncomputable def nb061_alpha_dummy_006 : Var := (freshVar (((Class.cv (nb061_alpha_dummy_001))).fv ∪ ((Class.cv (nb061_alpha_dummy_000))).fv) 1)

noncomputable def nb061_alpha_dummy_007 (r : Var) (a : Var) : Var := (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0)

noncomputable def nb061_alpha_dummy_008 (r : Var) (a : Var) : Var := (freshVar (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1)

noncomputable def nb061_alpha_dummy_009 : Var := (freshVar (((syn_ccompl (Class.cab (nb061_alpha_dummy_005) (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_001)) (Wff.classEq (Class.cv (nb061_alpha_dummy_005)) (syn_cphi (Class.cv (nb061_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl (Class.cab (nb061_alpha_dummy_005) (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_000)) (Wff.classEq (Class.cv (nb061_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_006))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb061_alpha_dummy_010 (r : Var) (a : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb061_alpha_dummy_007 r a) (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv r) (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a)) (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))))))).fv ∪ ((syn_ccompl (Class.cab (nb061_alpha_dummy_007 r a) (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv a) (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb061_alpha_dummy_011 : Var := (freshVar (((Class.cab (nb061_alpha_dummy_005) (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_001)) (Wff.classEq (Class.cv (nb061_alpha_dummy_005)) (syn_cphi (Class.cv (nb061_alpha_dummy_006))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_005) (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_001)) (Wff.classEq (Class.cv (nb061_alpha_dummy_005)) (syn_cphi (Class.cv (nb061_alpha_dummy_006))))))).fv) 0)

noncomputable def nb061_alpha_dummy_012 (r : Var) (a : Var) : Var := (freshVar (((Class.cab (nb061_alpha_dummy_007 r a) (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv r) (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a)) (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_007 r a) (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv r) (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a)) (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))))))).fv) 0)

noncomputable def nb061_alpha_dummy_013 : Var := (freshVar (((Class.cv (nb061_alpha_dummy_006))).fv) 0)

noncomputable def nb061_alpha_dummy_014 : Var := (freshVar (((Class.cv (nb061_alpha_dummy_006))).fv) 1)

noncomputable def nb061_alpha_dummy_015 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb061_alpha_dummy_008 r a))).fv) 0)

noncomputable def nb061_alpha_dummy_016 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb061_alpha_dummy_008 r a))).fv) 1)

noncomputable def nb061_alpha_dummy_017 : Var := (freshVar (((Wff.classMem (Class.cv (nb061_alpha_dummy_013)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb061_alpha_dummy_013)) (syn_c1c))).fv ∪ ((Class.cv (nb061_alpha_dummy_013))).fv) 0)

noncomputable def nb061_alpha_dummy_018 (r : Var) (a : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb061_alpha_dummy_015 r a)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb061_alpha_dummy_015 r a)) (syn_c1c))).fv ∪ ((Class.cv (nb061_alpha_dummy_015 r a))).fv) 0)

noncomputable def nb061_alpha_dummy_019 : Var := (freshVar (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb061_alpha_dummy_020 : Var := (freshVar (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb061_alpha_dummy_021 : Var := (freshVar (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb061_alpha_dummy_022 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb061_alpha_dummy_023 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb061_alpha_dummy_024 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb061_alpha_dummy_025 : Var := (freshVar (((syn_cnin (Class.cv (nb061_alpha_dummy_020)) (Class.cv (nb061_alpha_dummy_021)))).fv ∪ ((syn_cnin (Class.cv (nb061_alpha_dummy_020)) (Class.cv (nb061_alpha_dummy_021)))).fv) 0)

noncomputable def nb061_alpha_dummy_026 (r : Var) (a : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb061_alpha_dummy_023 r a)) (Class.cv (nb061_alpha_dummy_024 r a)))).fv ∪ ((syn_cnin (Class.cv (nb061_alpha_dummy_023 r a)) (Class.cv (nb061_alpha_dummy_024 r a)))).fv) 0)

noncomputable def nb061_alpha_dummy_027 : Var := (freshVar (((Class.cv (nb061_alpha_dummy_020))).fv ∪ ((Class.cv (nb061_alpha_dummy_021))).fv) 0)

noncomputable def nb061_alpha_dummy_028 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb061_alpha_dummy_023 r a))).fv ∪ ((Class.cv (nb061_alpha_dummy_024 r a))).fv) 0)

noncomputable def nb061_alpha_dummy_029 : Var := (freshVar (((syn_ccompl (Class.cv (nb061_alpha_dummy_020)))).fv ∪ ((syn_ccompl (Class.cv (nb061_alpha_dummy_021)))).fv) 0)

noncomputable def nb061_alpha_dummy_030 (r : Var) (a : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb061_alpha_dummy_023 r a)))).fv ∪ ((syn_ccompl (Class.cv (nb061_alpha_dummy_024 r a)))).fv) 0)

noncomputable def nb061_alpha_dummy_031 : Var := (freshVar (((Class.cv (nb061_alpha_dummy_020))).fv ∪ ((Class.cv (nb061_alpha_dummy_020))).fv) 0)

noncomputable def nb061_alpha_dummy_032 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb061_alpha_dummy_023 r a))).fv ∪ ((Class.cv (nb061_alpha_dummy_023 r a))).fv) 0)

noncomputable def nb061_alpha_dummy_033 : Var := (freshVar (((Class.cv (nb061_alpha_dummy_021))).fv ∪ ((Class.cv (nb061_alpha_dummy_021))).fv) 0)

noncomputable def nb061_alpha_dummy_034 (r : Var) (a : Var) : Var := (freshVar (((Class.cv (nb061_alpha_dummy_024 r a))).fv ∪ ((Class.cv (nb061_alpha_dummy_024 r a))).fv) 0)

noncomputable def nb061_alpha_dummy_035 : Var := (freshVar (((Class.cab (nb061_alpha_dummy_005) (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_000)) (Wff.classEq (Class.cv (nb061_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_005) (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_000)) (Wff.classEq (Class.cv (nb061_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb061_alpha_dummy_036 (r : Var) (a : Var) : Var := (freshVar (((Class.cab (nb061_alpha_dummy_007 r a) (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv a) (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_007 r a) (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv a) (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb061_alpha_dummy_037 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb061_alpha_dummy_006))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb061_alpha_dummy_038 (r : Var) (a : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb061_alpha_dummy_039 : Var := (freshVar (((syn_cphi (Class.cv (nb061_alpha_dummy_006)))).fv ∪ ((syn_cphi (Class.cv (nb061_alpha_dummy_006)))).fv) 0)

noncomputable def nb061_alpha_dummy_040 (r : Var) (a : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))).fv ∪ ((syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))).fv) 0)

noncomputable def nb061_alpha_dummy_041 : Var := (freshVar (((Class.cv (nb061_alpha_dummy_002))).fv ∪ ((Class.cv (nb061_alpha_dummy_002))).fv) 0)

noncomputable def nb061_alpha_dummy_042 : Var := (freshVar (((Class.cv (nb061_alpha_dummy_002))).fv ∪ ((Class.cv (nb061_alpha_dummy_002))).fv) 1)

noncomputable def nb061_alpha_dummy_043 (x : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv x)).fv) 0)

noncomputable def nb061_alpha_dummy_044 (x : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv x)).fv) 1)

noncomputable def nb061_alpha_dummy_045 : Var := (freshVar (((syn_ccompl (Class.cab (nb061_alpha_dummy_041) (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002)) (Wff.classEq (Class.cv (nb061_alpha_dummy_041)) (syn_cphi (Class.cv (nb061_alpha_dummy_042)))))))).fv ∪ ((syn_ccompl (Class.cab (nb061_alpha_dummy_041) (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002)) (Wff.classEq (Class.cv (nb061_alpha_dummy_041)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_042))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb061_alpha_dummy_046 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x) (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x)) (syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x) (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb061_alpha_dummy_047 : Var := (freshVar (((Class.cab (nb061_alpha_dummy_041) (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002)) (Wff.classEq (Class.cv (nb061_alpha_dummy_041)) (syn_cphi (Class.cv (nb061_alpha_dummy_042))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_041) (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002)) (Wff.classEq (Class.cv (nb061_alpha_dummy_041)) (syn_cphi (Class.cv (nb061_alpha_dummy_042))))))).fv) 0)

noncomputable def nb061_alpha_dummy_048 (x : Var) : Var := (freshVar (((Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x) (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x)) (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x) (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x)) (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))))))).fv) 0)

noncomputable def nb061_alpha_dummy_049 : Var := (freshVar (((Class.cv (nb061_alpha_dummy_042))).fv) 0)

noncomputable def nb061_alpha_dummy_050 : Var := (freshVar (((Class.cv (nb061_alpha_dummy_042))).fv) 1)

noncomputable def nb061_alpha_dummy_051 (x : Var) : Var := (freshVar (((Class.cv (nb061_alpha_dummy_044 x))).fv) 0)

noncomputable def nb061_alpha_dummy_052 (x : Var) : Var := (freshVar (((Class.cv (nb061_alpha_dummy_044 x))).fv) 1)

noncomputable def nb061_alpha_dummy_053 : Var := (freshVar (((Wff.classMem (Class.cv (nb061_alpha_dummy_049)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb061_alpha_dummy_049)) (syn_c1c))).fv ∪ ((Class.cv (nb061_alpha_dummy_049))).fv) 0)

noncomputable def nb061_alpha_dummy_054 (x : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb061_alpha_dummy_051 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb061_alpha_dummy_051 x)) (syn_c1c))).fv ∪ ((Class.cv (nb061_alpha_dummy_051 x))).fv) 0)

noncomputable def nb061_alpha_dummy_055 : Var := (freshVar (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb061_alpha_dummy_056 : Var := (freshVar (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb061_alpha_dummy_057 : Var := (freshVar (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb061_alpha_dummy_058 (x : Var) : Var := (freshVar (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb061_alpha_dummy_059 (x : Var) : Var := (freshVar (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb061_alpha_dummy_060 (x : Var) : Var := (freshVar (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb061_alpha_dummy_061 : Var := (freshVar (((syn_cnin (Class.cv (nb061_alpha_dummy_056)) (Class.cv (nb061_alpha_dummy_057)))).fv ∪ ((syn_cnin (Class.cv (nb061_alpha_dummy_056)) (Class.cv (nb061_alpha_dummy_057)))).fv) 0)

noncomputable def nb061_alpha_dummy_062 (x : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb061_alpha_dummy_059 x)) (Class.cv (nb061_alpha_dummy_060 x)))).fv ∪ ((syn_cnin (Class.cv (nb061_alpha_dummy_059 x)) (Class.cv (nb061_alpha_dummy_060 x)))).fv) 0)

noncomputable def nb061_alpha_dummy_063 : Var := (freshVar (((Class.cv (nb061_alpha_dummy_056))).fv ∪ ((Class.cv (nb061_alpha_dummy_057))).fv) 0)

noncomputable def nb061_alpha_dummy_064 (x : Var) : Var := (freshVar (((Class.cv (nb061_alpha_dummy_059 x))).fv ∪ ((Class.cv (nb061_alpha_dummy_060 x))).fv) 0)

noncomputable def nb061_alpha_dummy_065 : Var := (freshVar (((syn_ccompl (Class.cv (nb061_alpha_dummy_056)))).fv ∪ ((syn_ccompl (Class.cv (nb061_alpha_dummy_057)))).fv) 0)

noncomputable def nb061_alpha_dummy_066 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb061_alpha_dummy_059 x)))).fv ∪ ((syn_ccompl (Class.cv (nb061_alpha_dummy_060 x)))).fv) 0)

noncomputable def nb061_alpha_dummy_067 : Var := (freshVar (((Class.cv (nb061_alpha_dummy_056))).fv ∪ ((Class.cv (nb061_alpha_dummy_056))).fv) 0)

noncomputable def nb061_alpha_dummy_068 (x : Var) : Var := (freshVar (((Class.cv (nb061_alpha_dummy_059 x))).fv ∪ ((Class.cv (nb061_alpha_dummy_059 x))).fv) 0)

noncomputable def nb061_alpha_dummy_069 : Var := (freshVar (((Class.cv (nb061_alpha_dummy_057))).fv ∪ ((Class.cv (nb061_alpha_dummy_057))).fv) 0)

noncomputable def nb061_alpha_dummy_070 (x : Var) : Var := (freshVar (((Class.cv (nb061_alpha_dummy_060 x))).fv ∪ ((Class.cv (nb061_alpha_dummy_060 x))).fv) 0)

noncomputable def nb061_alpha_dummy_071 : Var := (freshVar (((Class.cab (nb061_alpha_dummy_041) (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002)) (Wff.classEq (Class.cv (nb061_alpha_dummy_041)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_042))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_041) (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002)) (Wff.classEq (Class.cv (nb061_alpha_dummy_041)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_042))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb061_alpha_dummy_072 (x : Var) : Var := (freshVar (((Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x) (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x) (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb061_alpha_dummy_073 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb061_alpha_dummy_042))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb061_alpha_dummy_074 (x : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb061_alpha_dummy_075 : Var := (freshVar (((syn_cphi (Class.cv (nb061_alpha_dummy_042)))).fv ∪ ((syn_cphi (Class.cv (nb061_alpha_dummy_042)))).fv) 0)

noncomputable def nb061_alpha_dummy_076 (x : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))).fv ∪ ((syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))).fv) 0)

theorem nb061_fresh_000 : (nb061_alpha_dummy_035) ∉ (((Class.cab (nb061_alpha_dummy_005) (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_000)) (Wff.classEq (Class.cv (nb061_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_005) (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_000)) (Wff.classEq (Class.cv (nb061_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb061_alpha_dummy_035] using freshVar_not_mem (((Class.cab (nb061_alpha_dummy_005) (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_000)) (Wff.classEq (Class.cv (nb061_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_005) (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_000)) (Wff.classEq (Class.cv (nb061_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb061_fresh_001 : (nb061_alpha_dummy_011) ∉ (((Class.cab (nb061_alpha_dummy_005) (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_001)) (Wff.classEq (Class.cv (nb061_alpha_dummy_005)) (syn_cphi (Class.cv (nb061_alpha_dummy_006))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_005) (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_001)) (Wff.classEq (Class.cv (nb061_alpha_dummy_005)) (syn_cphi (Class.cv (nb061_alpha_dummy_006))))))).fv) := by
  simpa only [nb061_alpha_dummy_011] using freshVar_not_mem (((Class.cab (nb061_alpha_dummy_005) (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_001)) (Wff.classEq (Class.cv (nb061_alpha_dummy_005)) (syn_cphi (Class.cv (nb061_alpha_dummy_006))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_005) (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_001)) (Wff.classEq (Class.cv (nb061_alpha_dummy_005)) (syn_cphi (Class.cv (nb061_alpha_dummy_006))))))).fv) 0

theorem nb061_fresh_002 (r : Var) (a : Var) : (nb061_alpha_dummy_036 r a) ∉ (((Class.cab (nb061_alpha_dummy_007 r a) (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv a) (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_007 r a) (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv a) (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb061_alpha_dummy_036] using freshVar_not_mem (((Class.cab (nb061_alpha_dummy_007 r a) (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv a) (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_007 r a) (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv a) (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb061_fresh_003 (r : Var) (a : Var) : (nb061_alpha_dummy_012 r a) ∉ (((Class.cab (nb061_alpha_dummy_007 r a) (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv r) (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a)) (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_007 r a) (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv r) (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a)) (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))))))).fv) := by
  simpa only [nb061_alpha_dummy_012] using freshVar_not_mem (((Class.cab (nb061_alpha_dummy_007 r a) (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv r) (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a)) (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_007 r a) (syn_wrex (nb061_alpha_dummy_008 r a) (Class.cv r) (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a)) (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a))))))).fv) 0

theorem nb061_fresh_004 : (nb061_alpha_dummy_047) ∉ (((Class.cab (nb061_alpha_dummy_041) (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002)) (Wff.classEq (Class.cv (nb061_alpha_dummy_041)) (syn_cphi (Class.cv (nb061_alpha_dummy_042))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_041) (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002)) (Wff.classEq (Class.cv (nb061_alpha_dummy_041)) (syn_cphi (Class.cv (nb061_alpha_dummy_042))))))).fv) := by
  simpa only [nb061_alpha_dummy_047] using freshVar_not_mem (((Class.cab (nb061_alpha_dummy_041) (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002)) (Wff.classEq (Class.cv (nb061_alpha_dummy_041)) (syn_cphi (Class.cv (nb061_alpha_dummy_042))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_041) (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002)) (Wff.classEq (Class.cv (nb061_alpha_dummy_041)) (syn_cphi (Class.cv (nb061_alpha_dummy_042))))))).fv) 0

theorem nb061_fresh_005 : (nb061_alpha_dummy_071) ∉ (((Class.cab (nb061_alpha_dummy_041) (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002)) (Wff.classEq (Class.cv (nb061_alpha_dummy_041)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_042))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_041) (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002)) (Wff.classEq (Class.cv (nb061_alpha_dummy_041)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_042))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb061_alpha_dummy_071] using freshVar_not_mem (((Class.cab (nb061_alpha_dummy_041) (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002)) (Wff.classEq (Class.cv (nb061_alpha_dummy_041)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_042))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_041) (syn_wrex (nb061_alpha_dummy_042) (Class.cv (nb061_alpha_dummy_002)) (Wff.classEq (Class.cv (nb061_alpha_dummy_041)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_042))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb061_fresh_006 (x : Var) : (nb061_alpha_dummy_048 x) ∉ (((Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x) (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x)) (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x) (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x)) (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))))))).fv) := by
  simpa only [nb061_alpha_dummy_048] using freshVar_not_mem (((Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x) (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x)) (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x) (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x)) (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))))))).fv) 0

theorem nb061_fresh_007 (x : Var) : (nb061_alpha_dummy_072 x) ∉ (((Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x) (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x) (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb061_alpha_dummy_072] using freshVar_not_mem (((Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x) (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb061_alpha_dummy_043 x) (syn_wrex (nb061_alpha_dummy_044 x) (Class.cv x) (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_044 x))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb061_fresh_008 : (nb061_alpha_dummy_005) ∉ (((Class.cv (nb061_alpha_dummy_001))).fv ∪ ((Class.cv (nb061_alpha_dummy_000))).fv) := by
  simpa only [nb061_alpha_dummy_005] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_001))).fv ∪ ((Class.cv (nb061_alpha_dummy_000))).fv) 0

theorem nb061_fresh_009 : (nb061_alpha_dummy_006) ∉ (((Class.cv (nb061_alpha_dummy_001))).fv ∪ ((Class.cv (nb061_alpha_dummy_000))).fv) := by
  simpa only [nb061_alpha_dummy_006] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_001))).fv ∪ ((Class.cv (nb061_alpha_dummy_000))).fv) 1

theorem nb061_distinct_010 : (nb061_alpha_dummy_005) ≠ (nb061_alpha_dummy_006) := by
  simpa only [nb061_alpha_dummy_005, nb061_alpha_dummy_006] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_001))).fv ∪ ((Class.cv (nb061_alpha_dummy_000))).fv) (i := 0) (j := 1) (by decide))

theorem nb061_fresh_011 : (nb061_alpha_dummy_041) ∉ (((Class.cv (nb061_alpha_dummy_002))).fv ∪ ((Class.cv (nb061_alpha_dummy_002))).fv) := by
  simpa only [nb061_alpha_dummy_041] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_002))).fv ∪ ((Class.cv (nb061_alpha_dummy_002))).fv) 0

theorem nb061_fresh_012 : (nb061_alpha_dummy_042) ∉ (((Class.cv (nb061_alpha_dummy_002))).fv ∪ ((Class.cv (nb061_alpha_dummy_002))).fv) := by
  simpa only [nb061_alpha_dummy_042] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_002))).fv ∪ ((Class.cv (nb061_alpha_dummy_002))).fv) 1

theorem nb061_distinct_013 : (nb061_alpha_dummy_041) ≠ (nb061_alpha_dummy_042) := by
  simpa only [nb061_alpha_dummy_041, nb061_alpha_dummy_042] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_002))).fv ∪ ((Class.cv (nb061_alpha_dummy_002))).fv) (i := 0) (j := 1) (by decide))

theorem nb061_fresh_014 : (nb061_alpha_dummy_013) ∉ (((Class.cv (nb061_alpha_dummy_006))).fv) := by
  simpa only [nb061_alpha_dummy_013] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_006))).fv) 0

theorem nb061_fresh_015 : (nb061_alpha_dummy_014) ∉ (((Class.cv (nb061_alpha_dummy_006))).fv) := by
  simpa only [nb061_alpha_dummy_014] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_006))).fv) 1

theorem nb061_distinct_016 : (nb061_alpha_dummy_013) ≠ (nb061_alpha_dummy_014) := by
  simpa only [nb061_alpha_dummy_013, nb061_alpha_dummy_014] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_006))).fv) (i := 0) (j := 1) (by decide))

theorem nb061_fresh_017 (r : Var) (a : Var) : (nb061_alpha_dummy_015 r a) ∉ (((Class.cv (nb061_alpha_dummy_008 r a))).fv) := by
  simpa only [nb061_alpha_dummy_015] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_008 r a))).fv) 0

theorem nb061_fresh_018 (r : Var) (a : Var) : (nb061_alpha_dummy_016 r a) ∉ (((Class.cv (nb061_alpha_dummy_008 r a))).fv) := by
  simpa only [nb061_alpha_dummy_016] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_008 r a))).fv) 1

theorem nb061_distinct_019 (r : Var) (a : Var) : (nb061_alpha_dummy_015 r a) ≠ (nb061_alpha_dummy_016 r a) := by
  simpa only [nb061_alpha_dummy_015, nb061_alpha_dummy_016] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_008 r a))).fv) (i := 0) (j := 1) (by decide))

theorem nb061_fresh_020 : (nb061_alpha_dummy_019) ∉ (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb061_alpha_dummy_019] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 0

theorem nb061_fresh_021 : (nb061_alpha_dummy_020) ∉ (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb061_alpha_dummy_020] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 1

theorem nb061_fresh_022 : (nb061_alpha_dummy_021) ∉ (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb061_alpha_dummy_021] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 2

theorem nb061_distinct_023 : (nb061_alpha_dummy_019) ≠ (nb061_alpha_dummy_020) := by
  simpa only [nb061_alpha_dummy_019, nb061_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb061_distinct_024 : (nb061_alpha_dummy_019) ≠ (nb061_alpha_dummy_021) := by
  simpa only [nb061_alpha_dummy_019, nb061_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb061_distinct_025 : (nb061_alpha_dummy_020) ≠ (nb061_alpha_dummy_021) := by
  simpa only [nb061_alpha_dummy_020, nb061_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb061_fresh_026 (r : Var) (a : Var) : (nb061_alpha_dummy_022 r a) ∉ (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb061_alpha_dummy_022] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv) 0

theorem nb061_fresh_027 (r : Var) (a : Var) : (nb061_alpha_dummy_023 r a) ∉ (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb061_alpha_dummy_023] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv) 1

theorem nb061_fresh_028 (r : Var) (a : Var) : (nb061_alpha_dummy_024 r a) ∉ (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb061_alpha_dummy_024] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv) 2

theorem nb061_distinct_029 (r : Var) (a : Var) : (nb061_alpha_dummy_022 r a) ≠ (nb061_alpha_dummy_023 r a) := by
  simpa only [nb061_alpha_dummy_022, nb061_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb061_distinct_030 (r : Var) (a : Var) : (nb061_alpha_dummy_022 r a) ≠ (nb061_alpha_dummy_024 r a) := by
  simpa only [nb061_alpha_dummy_022, nb061_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb061_distinct_031 (r : Var) (a : Var) : (nb061_alpha_dummy_023 r a) ≠ (nb061_alpha_dummy_024 r a) := by
  simpa only [nb061_alpha_dummy_023, nb061_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb061_fresh_032 : (nb061_alpha_dummy_031) ∉ (((Class.cv (nb061_alpha_dummy_020))).fv ∪ ((Class.cv (nb061_alpha_dummy_020))).fv) := by
  simpa only [nb061_alpha_dummy_031] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_020))).fv ∪ ((Class.cv (nb061_alpha_dummy_020))).fv) 0

theorem nb061_fresh_033 : (nb061_alpha_dummy_027) ∉ (((Class.cv (nb061_alpha_dummy_020))).fv ∪ ((Class.cv (nb061_alpha_dummy_021))).fv) := by
  simpa only [nb061_alpha_dummy_027] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_020))).fv ∪ ((Class.cv (nb061_alpha_dummy_021))).fv) 0

theorem nb061_fresh_034 : (nb061_alpha_dummy_033) ∉ (((Class.cv (nb061_alpha_dummy_021))).fv ∪ ((Class.cv (nb061_alpha_dummy_021))).fv) := by
  simpa only [nb061_alpha_dummy_033] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_021))).fv ∪ ((Class.cv (nb061_alpha_dummy_021))).fv) 0

theorem nb061_fresh_035 (r : Var) (a : Var) : (nb061_alpha_dummy_032 r a) ∉ (((Class.cv (nb061_alpha_dummy_023 r a))).fv ∪ ((Class.cv (nb061_alpha_dummy_023 r a))).fv) := by
  simpa only [nb061_alpha_dummy_032] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_023 r a))).fv ∪ ((Class.cv (nb061_alpha_dummy_023 r a))).fv) 0

theorem nb061_fresh_036 (r : Var) (a : Var) : (nb061_alpha_dummy_028 r a) ∉ (((Class.cv (nb061_alpha_dummy_023 r a))).fv ∪ ((Class.cv (nb061_alpha_dummy_024 r a))).fv) := by
  simpa only [nb061_alpha_dummy_028] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_023 r a))).fv ∪ ((Class.cv (nb061_alpha_dummy_024 r a))).fv) 0

theorem nb061_fresh_037 (r : Var) (a : Var) : (nb061_alpha_dummy_034 r a) ∉ (((Class.cv (nb061_alpha_dummy_024 r a))).fv ∪ ((Class.cv (nb061_alpha_dummy_024 r a))).fv) := by
  simpa only [nb061_alpha_dummy_034] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_024 r a))).fv ∪ ((Class.cv (nb061_alpha_dummy_024 r a))).fv) 0

theorem nb061_fresh_038 : (nb061_alpha_dummy_049) ∉ (((Class.cv (nb061_alpha_dummy_042))).fv) := by
  simpa only [nb061_alpha_dummy_049] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_042))).fv) 0

theorem nb061_fresh_039 : (nb061_alpha_dummy_050) ∉ (((Class.cv (nb061_alpha_dummy_042))).fv) := by
  simpa only [nb061_alpha_dummy_050] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_042))).fv) 1

theorem nb061_distinct_040 : (nb061_alpha_dummy_049) ≠ (nb061_alpha_dummy_050) := by
  simpa only [nb061_alpha_dummy_049, nb061_alpha_dummy_050] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_042))).fv) (i := 0) (j := 1) (by decide))

theorem nb061_fresh_041 (x : Var) : (nb061_alpha_dummy_051 x) ∉ (((Class.cv (nb061_alpha_dummy_044 x))).fv) := by
  simpa only [nb061_alpha_dummy_051] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_044 x))).fv) 0

theorem nb061_fresh_042 (x : Var) : (nb061_alpha_dummy_052 x) ∉ (((Class.cv (nb061_alpha_dummy_044 x))).fv) := by
  simpa only [nb061_alpha_dummy_052] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_044 x))).fv) 1

theorem nb061_distinct_043 (x : Var) : (nb061_alpha_dummy_051 x) ≠ (nb061_alpha_dummy_052 x) := by
  simpa only [nb061_alpha_dummy_051, nb061_alpha_dummy_052] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_044 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb061_fresh_044 : (nb061_alpha_dummy_055) ∉ (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb061_alpha_dummy_055] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) 0

theorem nb061_fresh_045 : (nb061_alpha_dummy_056) ∉ (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb061_alpha_dummy_056] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) 1

theorem nb061_fresh_046 : (nb061_alpha_dummy_057) ∉ (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb061_alpha_dummy_057] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) 2

theorem nb061_distinct_047 : (nb061_alpha_dummy_055) ≠ (nb061_alpha_dummy_056) := by
  simpa only [nb061_alpha_dummy_055, nb061_alpha_dummy_056] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb061_distinct_048 : (nb061_alpha_dummy_055) ≠ (nb061_alpha_dummy_057) := by
  simpa only [nb061_alpha_dummy_055, nb061_alpha_dummy_057] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb061_distinct_049 : (nb061_alpha_dummy_056) ≠ (nb061_alpha_dummy_057) := by
  simpa only [nb061_alpha_dummy_056, nb061_alpha_dummy_057] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb061_fresh_050 (x : Var) : (nb061_alpha_dummy_058 x) ∉ (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb061_alpha_dummy_058] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb061_fresh_051 (x : Var) : (nb061_alpha_dummy_059 x) ∉ (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb061_alpha_dummy_059] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb061_fresh_052 (x : Var) : (nb061_alpha_dummy_060 x) ∉ (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb061_alpha_dummy_060] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb061_distinct_053 (x : Var) : (nb061_alpha_dummy_058 x) ≠ (nb061_alpha_dummy_059 x) := by
  simpa only [nb061_alpha_dummy_058, nb061_alpha_dummy_059] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb061_distinct_054 (x : Var) : (nb061_alpha_dummy_058 x) ≠ (nb061_alpha_dummy_060 x) := by
  simpa only [nb061_alpha_dummy_058, nb061_alpha_dummy_060] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb061_distinct_055 (x : Var) : (nb061_alpha_dummy_059 x) ≠ (nb061_alpha_dummy_060 x) := by
  simpa only [nb061_alpha_dummy_059, nb061_alpha_dummy_060] using
    (freshVar_injective (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb061_fresh_056 : (nb061_alpha_dummy_067) ∉ (((Class.cv (nb061_alpha_dummy_056))).fv ∪ ((Class.cv (nb061_alpha_dummy_056))).fv) := by
  simpa only [nb061_alpha_dummy_067] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_056))).fv ∪ ((Class.cv (nb061_alpha_dummy_056))).fv) 0

theorem nb061_fresh_057 : (nb061_alpha_dummy_063) ∉ (((Class.cv (nb061_alpha_dummy_056))).fv ∪ ((Class.cv (nb061_alpha_dummy_057))).fv) := by
  simpa only [nb061_alpha_dummy_063] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_056))).fv ∪ ((Class.cv (nb061_alpha_dummy_057))).fv) 0

theorem nb061_fresh_058 : (nb061_alpha_dummy_069) ∉ (((Class.cv (nb061_alpha_dummy_057))).fv ∪ ((Class.cv (nb061_alpha_dummy_057))).fv) := by
  simpa only [nb061_alpha_dummy_069] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_057))).fv ∪ ((Class.cv (nb061_alpha_dummy_057))).fv) 0

theorem nb061_fresh_059 (x : Var) : (nb061_alpha_dummy_068 x) ∉ (((Class.cv (nb061_alpha_dummy_059 x))).fv ∪ ((Class.cv (nb061_alpha_dummy_059 x))).fv) := by
  simpa only [nb061_alpha_dummy_068] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_059 x))).fv ∪ ((Class.cv (nb061_alpha_dummy_059 x))).fv) 0

theorem nb061_fresh_060 (x : Var) : (nb061_alpha_dummy_064 x) ∉ (((Class.cv (nb061_alpha_dummy_059 x))).fv ∪ ((Class.cv (nb061_alpha_dummy_060 x))).fv) := by
  simpa only [nb061_alpha_dummy_064] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_059 x))).fv ∪ ((Class.cv (nb061_alpha_dummy_060 x))).fv) 0

theorem nb061_fresh_061 (x : Var) : (nb061_alpha_dummy_070 x) ∉ (((Class.cv (nb061_alpha_dummy_060 x))).fv ∪ ((Class.cv (nb061_alpha_dummy_060 x))).fv) := by
  simpa only [nb061_alpha_dummy_070] using freshVar_not_mem (((Class.cv (nb061_alpha_dummy_060 x))).fv ∪ ((Class.cv (nb061_alpha_dummy_060 x))).fv) 0

theorem nb061_fresh_062 (r : Var) (a : Var) : (nb061_alpha_dummy_007 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb061_alpha_dummy_007] using freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0

theorem nb061_fresh_063 (r : Var) (a : Var) : (nb061_alpha_dummy_008 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb061_alpha_dummy_008] using freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1

theorem nb061_distinct_064 (r : Var) (a : Var) : (nb061_alpha_dummy_007 r a) ≠ (nb061_alpha_dummy_008 r a) := by
  simpa only [nb061_alpha_dummy_007, nb061_alpha_dummy_008] using
    (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (i := 0) (j := 1) (by decide))

theorem nb061_fresh_065 (x : Var) : (nb061_alpha_dummy_043 x) ∉ (((Class.cv x)).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb061_alpha_dummy_043] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv x)).fv) 0

theorem nb061_fresh_066 (x : Var) : (nb061_alpha_dummy_044 x) ∉ (((Class.cv x)).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb061_alpha_dummy_044] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv x)).fv) 1

theorem nb061_distinct_067 (x : Var) : (nb061_alpha_dummy_043 x) ≠ (nb061_alpha_dummy_044 x) := by
  simpa only [nb061_alpha_dummy_043, nb061_alpha_dummy_044] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv x)).fv) (i := 0) (j := 1) (by decide))

theorem nb061_fresh_068 : (nb061_alpha_dummy_017) ∉ (((Wff.classMem (Class.cv (nb061_alpha_dummy_013)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb061_alpha_dummy_013)) (syn_c1c))).fv ∪ ((Class.cv (nb061_alpha_dummy_013))).fv) := by
  simpa only [nb061_alpha_dummy_017] using freshVar_not_mem (((Wff.classMem (Class.cv (nb061_alpha_dummy_013)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb061_alpha_dummy_013)) (syn_c1c))).fv ∪ ((Class.cv (nb061_alpha_dummy_013))).fv) 0

theorem nb061_fresh_069 (r : Var) (a : Var) : (nb061_alpha_dummy_018 r a) ∉ (((Wff.classMem (Class.cv (nb061_alpha_dummy_015 r a)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb061_alpha_dummy_015 r a)) (syn_c1c))).fv ∪ ((Class.cv (nb061_alpha_dummy_015 r a))).fv) := by
  simpa only [nb061_alpha_dummy_018] using freshVar_not_mem (((Wff.classMem (Class.cv (nb061_alpha_dummy_015 r a)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb061_alpha_dummy_015 r a)) (syn_c1c))).fv ∪ ((Class.cv (nb061_alpha_dummy_015 r a))).fv) 0

theorem nb061_fresh_070 : (nb061_alpha_dummy_053) ∉ (((Wff.classMem (Class.cv (nb061_alpha_dummy_049)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb061_alpha_dummy_049)) (syn_c1c))).fv ∪ ((Class.cv (nb061_alpha_dummy_049))).fv) := by
  simpa only [nb061_alpha_dummy_053] using freshVar_not_mem (((Wff.classMem (Class.cv (nb061_alpha_dummy_049)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb061_alpha_dummy_049)) (syn_c1c))).fv ∪ ((Class.cv (nb061_alpha_dummy_049))).fv) 0

theorem nb061_fresh_071 (x : Var) : (nb061_alpha_dummy_054 x) ∉ (((Wff.classMem (Class.cv (nb061_alpha_dummy_051 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb061_alpha_dummy_051 x)) (syn_c1c))).fv ∪ ((Class.cv (nb061_alpha_dummy_051 x))).fv) := by
  simpa only [nb061_alpha_dummy_054] using freshVar_not_mem (((Wff.classMem (Class.cv (nb061_alpha_dummy_051 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb061_alpha_dummy_051 x)) (syn_c1c))).fv ∪ ((Class.cv (nb061_alpha_dummy_051 x))).fv) 0

theorem nb061_fresh_072 : (nb061_alpha_dummy_009) ∉ (((syn_ccompl (Class.cab (nb061_alpha_dummy_005) (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_001)) (Wff.classEq (Class.cv (nb061_alpha_dummy_005)) (syn_cphi (Class.cv (nb061_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl (Class.cab (nb061_alpha_dummy_005) (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_000)) (Wff.classEq (Class.cv (nb061_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_006))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb061_alpha_dummy_009] using freshVar_not_mem (((syn_ccompl (Class.cab (nb061_alpha_dummy_005) (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_001)) (Wff.classEq (Class.cv (nb061_alpha_dummy_005)) (syn_cphi (Class.cv (nb061_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl (Class.cab (nb061_alpha_dummy_005) (syn_wrex (nb061_alpha_dummy_006) (Class.cv (nb061_alpha_dummy_000)) (Wff.classEq (Class.cv (nb061_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb061_alpha_dummy_006))) (syn_csn (syn_c0c)))))))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
