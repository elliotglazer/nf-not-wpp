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

noncomputable def nb075_alpha_dummy_000 : Var := (freshVar ((∅ : Finset Var)) 0)

noncomputable def nb075_alpha_dummy_001 : Var := (freshVar (({(nb075_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_crn (Class.cv (nb075_alpha_dummy_000)))).fv) 0)

noncomputable def nb075_alpha_dummy_002 (x : Var) : Var := (freshVar (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_crn (Class.cv x))).fv) 0)

noncomputable def nb075_alpha_dummy_003 : Var := (freshVar (({(nb075_alpha_dummy_000)} : Finset Var) ∪ ({(nb075_alpha_dummy_001)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb075_alpha_dummy_000)) (syn_cvv)) (Wff.classEq (Class.cv (nb075_alpha_dummy_001)) (syn_crn (Class.cv (nb075_alpha_dummy_000)))))).fv) 0)

noncomputable def nb075_alpha_dummy_004 (x : Var) : Var := (freshVar (({x} : Finset Var) ∪ ({(nb075_alpha_dummy_002 x)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classEq (Class.cv (nb075_alpha_dummy_002 x)) (syn_crn (Class.cv x))))).fv) 0)

noncomputable def nb075_alpha_dummy_005 : Var := (freshVar (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((Class.cv (nb075_alpha_dummy_001))).fv) 0)

noncomputable def nb075_alpha_dummy_006 : Var := (freshVar (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((Class.cv (nb075_alpha_dummy_001))).fv) 1)

noncomputable def nb075_alpha_dummy_007 (x : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb075_alpha_dummy_002 x))).fv) 0)

noncomputable def nb075_alpha_dummy_008 (x : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb075_alpha_dummy_002 x))).fv) 1)

noncomputable def nb075_alpha_dummy_009 : Var := (freshVar (((syn_ccompl (Class.cab (nb075_alpha_dummy_005) (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_000)) (Wff.classEq (Class.cv (nb075_alpha_dummy_005)) (syn_cphi (Class.cv (nb075_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl (Class.cab (nb075_alpha_dummy_005) (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_001)) (Wff.classEq (Class.cv (nb075_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_006))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb075_alpha_dummy_010 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb075_alpha_dummy_007 x) (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb075_alpha_dummy_007 x) (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv (nb075_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb075_alpha_dummy_011 : Var := (freshVar (((Class.cab (nb075_alpha_dummy_005) (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_000)) (Wff.classEq (Class.cv (nb075_alpha_dummy_005)) (syn_cphi (Class.cv (nb075_alpha_dummy_006))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_005) (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_000)) (Wff.classEq (Class.cv (nb075_alpha_dummy_005)) (syn_cphi (Class.cv (nb075_alpha_dummy_006))))))).fv) 0)

noncomputable def nb075_alpha_dummy_012 (x : Var) : Var := (freshVar (((Class.cab (nb075_alpha_dummy_007 x) (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_007 x) (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))))))).fv) 0)

noncomputable def nb075_alpha_dummy_013 : Var := (freshVar (((Class.cv (nb075_alpha_dummy_006))).fv) 0)

noncomputable def nb075_alpha_dummy_014 : Var := (freshVar (((Class.cv (nb075_alpha_dummy_006))).fv) 1)

noncomputable def nb075_alpha_dummy_015 (x : Var) : Var := (freshVar (((Class.cv (nb075_alpha_dummy_008 x))).fv) 0)

noncomputable def nb075_alpha_dummy_016 (x : Var) : Var := (freshVar (((Class.cv (nb075_alpha_dummy_008 x))).fv) 1)

noncomputable def nb075_alpha_dummy_017 : Var := (freshVar (((Wff.classMem (Class.cv (nb075_alpha_dummy_013)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb075_alpha_dummy_013)) (syn_c1c))).fv ∪ ((Class.cv (nb075_alpha_dummy_013))).fv) 0)

noncomputable def nb075_alpha_dummy_018 (x : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb075_alpha_dummy_015 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb075_alpha_dummy_015 x)) (syn_c1c))).fv ∪ ((Class.cv (nb075_alpha_dummy_015 x))).fv) 0)

noncomputable def nb075_alpha_dummy_019 : Var := (freshVar (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb075_alpha_dummy_020 : Var := (freshVar (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb075_alpha_dummy_021 : Var := (freshVar (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb075_alpha_dummy_022 (x : Var) : Var := (freshVar (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb075_alpha_dummy_023 (x : Var) : Var := (freshVar (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb075_alpha_dummy_024 (x : Var) : Var := (freshVar (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb075_alpha_dummy_025 : Var := (freshVar (((syn_cnin (Class.cv (nb075_alpha_dummy_020)) (Class.cv (nb075_alpha_dummy_021)))).fv ∪ ((syn_cnin (Class.cv (nb075_alpha_dummy_020)) (Class.cv (nb075_alpha_dummy_021)))).fv) 0)

noncomputable def nb075_alpha_dummy_026 (x : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb075_alpha_dummy_023 x)) (Class.cv (nb075_alpha_dummy_024 x)))).fv ∪ ((syn_cnin (Class.cv (nb075_alpha_dummy_023 x)) (Class.cv (nb075_alpha_dummy_024 x)))).fv) 0)

noncomputable def nb075_alpha_dummy_027 : Var := (freshVar (((Class.cv (nb075_alpha_dummy_020))).fv ∪ ((Class.cv (nb075_alpha_dummy_021))).fv) 0)

noncomputable def nb075_alpha_dummy_028 (x : Var) : Var := (freshVar (((Class.cv (nb075_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_024 x))).fv) 0)

noncomputable def nb075_alpha_dummy_029 : Var := (freshVar (((syn_ccompl (Class.cv (nb075_alpha_dummy_020)))).fv ∪ ((syn_ccompl (Class.cv (nb075_alpha_dummy_021)))).fv) 0)

noncomputable def nb075_alpha_dummy_030 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb075_alpha_dummy_023 x)))).fv ∪ ((syn_ccompl (Class.cv (nb075_alpha_dummy_024 x)))).fv) 0)

noncomputable def nb075_alpha_dummy_031 : Var := (freshVar (((Class.cv (nb075_alpha_dummy_020))).fv ∪ ((Class.cv (nb075_alpha_dummy_020))).fv) 0)

noncomputable def nb075_alpha_dummy_032 (x : Var) : Var := (freshVar (((Class.cv (nb075_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_023 x))).fv) 0)

noncomputable def nb075_alpha_dummy_033 : Var := (freshVar (((Class.cv (nb075_alpha_dummy_021))).fv ∪ ((Class.cv (nb075_alpha_dummy_021))).fv) 0)

noncomputable def nb075_alpha_dummy_034 (x : Var) : Var := (freshVar (((Class.cv (nb075_alpha_dummy_024 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_024 x))).fv) 0)

noncomputable def nb075_alpha_dummy_035 : Var := (freshVar (((Class.cab (nb075_alpha_dummy_005) (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_001)) (Wff.classEq (Class.cv (nb075_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_005) (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_001)) (Wff.classEq (Class.cv (nb075_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb075_alpha_dummy_036 (x : Var) : Var := (freshVar (((Class.cab (nb075_alpha_dummy_007 x) (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv (nb075_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_007 x) (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv (nb075_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb075_alpha_dummy_037 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb075_alpha_dummy_006))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb075_alpha_dummy_038 (x : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb075_alpha_dummy_039 : Var := (freshVar (((syn_cphi (Class.cv (nb075_alpha_dummy_006)))).fv ∪ ((syn_cphi (Class.cv (nb075_alpha_dummy_006)))).fv) 0)

noncomputable def nb075_alpha_dummy_040 (x : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))).fv ∪ ((syn_cphi (Class.cv (nb075_alpha_dummy_008 x)))).fv) 0)

noncomputable def nb075_alpha_dummy_041 : Var := (freshVar (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb075_alpha_dummy_042 : Var := (freshVar (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb075_alpha_dummy_043 (x : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb075_alpha_dummy_044 (x : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb075_alpha_dummy_045 : Var := (freshVar (((Class.cv (nb075_alpha_dummy_042))).fv ∪ ((Class.cv (nb075_alpha_dummy_041))).fv) 0)

noncomputable def nb075_alpha_dummy_046 : Var := (freshVar (((Class.cv (nb075_alpha_dummy_042))).fv ∪ ((Class.cv (nb075_alpha_dummy_041))).fv) 1)

noncomputable def nb075_alpha_dummy_047 (x : Var) : Var := (freshVar (((Class.cv (nb075_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_043 x))).fv) 0)

noncomputable def nb075_alpha_dummy_048 (x : Var) : Var := (freshVar (((Class.cv (nb075_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_043 x))).fv) 1)

noncomputable def nb075_alpha_dummy_049 : Var := (freshVar (((syn_ccompl (Class.cab (nb075_alpha_dummy_045) (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_042)) (Wff.classEq (Class.cv (nb075_alpha_dummy_045)) (syn_cphi (Class.cv (nb075_alpha_dummy_046)))))))).fv ∪ ((syn_ccompl (Class.cab (nb075_alpha_dummy_045) (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_041)) (Wff.classEq (Class.cv (nb075_alpha_dummy_045)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_046))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb075_alpha_dummy_050 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb075_alpha_dummy_047 x) (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_044 x)) (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x)) (syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb075_alpha_dummy_047 x) (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_043 x)) (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb075_alpha_dummy_051 : Var := (freshVar (((Class.cab (nb075_alpha_dummy_045) (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_042)) (Wff.classEq (Class.cv (nb075_alpha_dummy_045)) (syn_cphi (Class.cv (nb075_alpha_dummy_046))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_045) (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_042)) (Wff.classEq (Class.cv (nb075_alpha_dummy_045)) (syn_cphi (Class.cv (nb075_alpha_dummy_046))))))).fv) 0)

noncomputable def nb075_alpha_dummy_052 (x : Var) : Var := (freshVar (((Class.cab (nb075_alpha_dummy_047 x) (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_044 x)) (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x)) (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_047 x) (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_044 x)) (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x)) (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))))))).fv) 0)

noncomputable def nb075_alpha_dummy_053 : Var := (freshVar (((Class.cv (nb075_alpha_dummy_046))).fv) 0)

noncomputable def nb075_alpha_dummy_054 : Var := (freshVar (((Class.cv (nb075_alpha_dummy_046))).fv) 1)

noncomputable def nb075_alpha_dummy_055 (x : Var) : Var := (freshVar (((Class.cv (nb075_alpha_dummy_048 x))).fv) 0)

noncomputable def nb075_alpha_dummy_056 (x : Var) : Var := (freshVar (((Class.cv (nb075_alpha_dummy_048 x))).fv) 1)

noncomputable def nb075_alpha_dummy_057 : Var := (freshVar (((Wff.classMem (Class.cv (nb075_alpha_dummy_053)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb075_alpha_dummy_053)) (syn_c1c))).fv ∪ ((Class.cv (nb075_alpha_dummy_053))).fv) 0)

noncomputable def nb075_alpha_dummy_058 (x : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb075_alpha_dummy_055 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb075_alpha_dummy_055 x)) (syn_c1c))).fv ∪ ((Class.cv (nb075_alpha_dummy_055 x))).fv) 0)

noncomputable def nb075_alpha_dummy_059 : Var := (freshVar (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb075_alpha_dummy_060 : Var := (freshVar (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb075_alpha_dummy_061 : Var := (freshVar (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb075_alpha_dummy_062 (x : Var) : Var := (freshVar (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb075_alpha_dummy_063 (x : Var) : Var := (freshVar (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb075_alpha_dummy_064 (x : Var) : Var := (freshVar (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb075_alpha_dummy_065 : Var := (freshVar (((syn_cnin (Class.cv (nb075_alpha_dummy_060)) (Class.cv (nb075_alpha_dummy_061)))).fv ∪ ((syn_cnin (Class.cv (nb075_alpha_dummy_060)) (Class.cv (nb075_alpha_dummy_061)))).fv) 0)

noncomputable def nb075_alpha_dummy_066 (x : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb075_alpha_dummy_063 x)) (Class.cv (nb075_alpha_dummy_064 x)))).fv ∪ ((syn_cnin (Class.cv (nb075_alpha_dummy_063 x)) (Class.cv (nb075_alpha_dummy_064 x)))).fv) 0)

noncomputable def nb075_alpha_dummy_067 : Var := (freshVar (((Class.cv (nb075_alpha_dummy_060))).fv ∪ ((Class.cv (nb075_alpha_dummy_061))).fv) 0)

noncomputable def nb075_alpha_dummy_068 (x : Var) : Var := (freshVar (((Class.cv (nb075_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_064 x))).fv) 0)

noncomputable def nb075_alpha_dummy_069 : Var := (freshVar (((syn_ccompl (Class.cv (nb075_alpha_dummy_060)))).fv ∪ ((syn_ccompl (Class.cv (nb075_alpha_dummy_061)))).fv) 0)

noncomputable def nb075_alpha_dummy_070 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb075_alpha_dummy_063 x)))).fv ∪ ((syn_ccompl (Class.cv (nb075_alpha_dummy_064 x)))).fv) 0)

noncomputable def nb075_alpha_dummy_071 : Var := (freshVar (((Class.cv (nb075_alpha_dummy_060))).fv ∪ ((Class.cv (nb075_alpha_dummy_060))).fv) 0)

noncomputable def nb075_alpha_dummy_072 (x : Var) : Var := (freshVar (((Class.cv (nb075_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_063 x))).fv) 0)

noncomputable def nb075_alpha_dummy_073 : Var := (freshVar (((Class.cv (nb075_alpha_dummy_061))).fv ∪ ((Class.cv (nb075_alpha_dummy_061))).fv) 0)

noncomputable def nb075_alpha_dummy_074 (x : Var) : Var := (freshVar (((Class.cv (nb075_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_064 x))).fv) 0)

noncomputable def nb075_alpha_dummy_075 : Var := (freshVar (((Class.cab (nb075_alpha_dummy_045) (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_041)) (Wff.classEq (Class.cv (nb075_alpha_dummy_045)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_046))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_045) (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_041)) (Wff.classEq (Class.cv (nb075_alpha_dummy_045)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_046))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb075_alpha_dummy_076 (x : Var) : Var := (freshVar (((Class.cab (nb075_alpha_dummy_047 x) (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_043 x)) (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_047 x) (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_043 x)) (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb075_alpha_dummy_077 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb075_alpha_dummy_046))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb075_alpha_dummy_078 (x : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb075_alpha_dummy_079 : Var := (freshVar (((syn_cphi (Class.cv (nb075_alpha_dummy_046)))).fv ∪ ((syn_cphi (Class.cv (nb075_alpha_dummy_046)))).fv) 0)

noncomputable def nb075_alpha_dummy_080 (x : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))).fv ∪ ((syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))).fv) 0)

theorem nb075_fresh_000 : (nb075_alpha_dummy_011) ∉ (((Class.cab (nb075_alpha_dummy_005) (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_000)) (Wff.classEq (Class.cv (nb075_alpha_dummy_005)) (syn_cphi (Class.cv (nb075_alpha_dummy_006))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_005) (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_000)) (Wff.classEq (Class.cv (nb075_alpha_dummy_005)) (syn_cphi (Class.cv (nb075_alpha_dummy_006))))))).fv) := by
  simpa only [nb075_alpha_dummy_011] using freshVar_not_mem (((Class.cab (nb075_alpha_dummy_005) (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_000)) (Wff.classEq (Class.cv (nb075_alpha_dummy_005)) (syn_cphi (Class.cv (nb075_alpha_dummy_006))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_005) (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_000)) (Wff.classEq (Class.cv (nb075_alpha_dummy_005)) (syn_cphi (Class.cv (nb075_alpha_dummy_006))))))).fv) 0

theorem nb075_fresh_001 : (nb075_alpha_dummy_035) ∉ (((Class.cab (nb075_alpha_dummy_005) (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_001)) (Wff.classEq (Class.cv (nb075_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_005) (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_001)) (Wff.classEq (Class.cv (nb075_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb075_alpha_dummy_035] using freshVar_not_mem (((Class.cab (nb075_alpha_dummy_005) (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_001)) (Wff.classEq (Class.cv (nb075_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_005) (syn_wrex (nb075_alpha_dummy_006) (Class.cv (nb075_alpha_dummy_001)) (Wff.classEq (Class.cv (nb075_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb075_fresh_002 (x : Var) : (nb075_alpha_dummy_036 x) ∉ (((Class.cab (nb075_alpha_dummy_007 x) (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv (nb075_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_007 x) (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv (nb075_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb075_alpha_dummy_036] using freshVar_not_mem (((Class.cab (nb075_alpha_dummy_007 x) (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv (nb075_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_007 x) (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv (nb075_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb075_fresh_003 (x : Var) : (nb075_alpha_dummy_012 x) ∉ (((Class.cab (nb075_alpha_dummy_007 x) (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_007 x) (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))))))).fv) := by
  simpa only [nb075_alpha_dummy_012] using freshVar_not_mem (((Class.cab (nb075_alpha_dummy_007 x) (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_007 x) (syn_wrex (nb075_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb075_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb075_alpha_dummy_008 x))))))).fv) 0

theorem nb075_fresh_004 : (nb075_alpha_dummy_075) ∉ (((Class.cab (nb075_alpha_dummy_045) (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_041)) (Wff.classEq (Class.cv (nb075_alpha_dummy_045)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_046))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_045) (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_041)) (Wff.classEq (Class.cv (nb075_alpha_dummy_045)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_046))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb075_alpha_dummy_075] using freshVar_not_mem (((Class.cab (nb075_alpha_dummy_045) (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_041)) (Wff.classEq (Class.cv (nb075_alpha_dummy_045)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_046))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_045) (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_041)) (Wff.classEq (Class.cv (nb075_alpha_dummy_045)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_046))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb075_fresh_005 : (nb075_alpha_dummy_051) ∉ (((Class.cab (nb075_alpha_dummy_045) (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_042)) (Wff.classEq (Class.cv (nb075_alpha_dummy_045)) (syn_cphi (Class.cv (nb075_alpha_dummy_046))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_045) (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_042)) (Wff.classEq (Class.cv (nb075_alpha_dummy_045)) (syn_cphi (Class.cv (nb075_alpha_dummy_046))))))).fv) := by
  simpa only [nb075_alpha_dummy_051] using freshVar_not_mem (((Class.cab (nb075_alpha_dummy_045) (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_042)) (Wff.classEq (Class.cv (nb075_alpha_dummy_045)) (syn_cphi (Class.cv (nb075_alpha_dummy_046))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_045) (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_042)) (Wff.classEq (Class.cv (nb075_alpha_dummy_045)) (syn_cphi (Class.cv (nb075_alpha_dummy_046))))))).fv) 0

theorem nb075_fresh_006 (x : Var) : (nb075_alpha_dummy_076 x) ∉ (((Class.cab (nb075_alpha_dummy_047 x) (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_043 x)) (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_047 x) (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_043 x)) (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb075_alpha_dummy_076] using freshVar_not_mem (((Class.cab (nb075_alpha_dummy_047 x) (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_043 x)) (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_047 x) (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_043 x)) (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x)) (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb075_fresh_007 (x : Var) : (nb075_alpha_dummy_052 x) ∉ (((Class.cab (nb075_alpha_dummy_047 x) (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_044 x)) (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x)) (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_047 x) (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_044 x)) (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x)) (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))))))).fv) := by
  simpa only [nb075_alpha_dummy_052] using freshVar_not_mem (((Class.cab (nb075_alpha_dummy_047 x) (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_044 x)) (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x)) (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))))))).fv ∪ ((Class.cab (nb075_alpha_dummy_047 x) (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_044 x)) (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x)) (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))))))).fv) 0

theorem nb075_fresh_008 : (nb075_alpha_dummy_005) ∉ (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((Class.cv (nb075_alpha_dummy_001))).fv) := by
  simpa only [nb075_alpha_dummy_005] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((Class.cv (nb075_alpha_dummy_001))).fv) 0

theorem nb075_fresh_009 : (nb075_alpha_dummy_006) ∉ (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((Class.cv (nb075_alpha_dummy_001))).fv) := by
  simpa only [nb075_alpha_dummy_006] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((Class.cv (nb075_alpha_dummy_001))).fv) 1

theorem nb075_distinct_010 : (nb075_alpha_dummy_005) ≠ (nb075_alpha_dummy_006) := by
  simpa only [nb075_alpha_dummy_005, nb075_alpha_dummy_006] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((Class.cv (nb075_alpha_dummy_001))).fv) (i := 0) (j := 1) (by decide))

theorem nb075_fresh_011 : (nb075_alpha_dummy_041) ∉ (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb075_alpha_dummy_041] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 0

theorem nb075_fresh_012 : (nb075_alpha_dummy_042) ∉ (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb075_alpha_dummy_042] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 1

theorem nb075_distinct_013 : (nb075_alpha_dummy_041) ≠ (nb075_alpha_dummy_042) := by
  simpa only [nb075_alpha_dummy_041, nb075_alpha_dummy_042] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb075_fresh_014 : (nb075_alpha_dummy_013) ∉ (((Class.cv (nb075_alpha_dummy_006))).fv) := by
  simpa only [nb075_alpha_dummy_013] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_006))).fv) 0

theorem nb075_fresh_015 : (nb075_alpha_dummy_014) ∉ (((Class.cv (nb075_alpha_dummy_006))).fv) := by
  simpa only [nb075_alpha_dummy_014] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_006))).fv) 1

theorem nb075_distinct_016 : (nb075_alpha_dummy_013) ≠ (nb075_alpha_dummy_014) := by
  simpa only [nb075_alpha_dummy_013, nb075_alpha_dummy_014] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_006))).fv) (i := 0) (j := 1) (by decide))

theorem nb075_fresh_017 (x : Var) : (nb075_alpha_dummy_015 x) ∉ (((Class.cv (nb075_alpha_dummy_008 x))).fv) := by
  simpa only [nb075_alpha_dummy_015] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_008 x))).fv) 0

theorem nb075_fresh_018 (x : Var) : (nb075_alpha_dummy_016 x) ∉ (((Class.cv (nb075_alpha_dummy_008 x))).fv) := by
  simpa only [nb075_alpha_dummy_016] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_008 x))).fv) 1

theorem nb075_distinct_019 (x : Var) : (nb075_alpha_dummy_015 x) ≠ (nb075_alpha_dummy_016 x) := by
  simpa only [nb075_alpha_dummy_015, nb075_alpha_dummy_016] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_008 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb075_fresh_020 : (nb075_alpha_dummy_019) ∉ (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb075_alpha_dummy_019] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 0

theorem nb075_fresh_021 : (nb075_alpha_dummy_020) ∉ (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb075_alpha_dummy_020] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 1

theorem nb075_fresh_022 : (nb075_alpha_dummy_021) ∉ (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb075_alpha_dummy_021] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 2

theorem nb075_distinct_023 : (nb075_alpha_dummy_019) ≠ (nb075_alpha_dummy_020) := by
  simpa only [nb075_alpha_dummy_019, nb075_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb075_distinct_024 : (nb075_alpha_dummy_019) ≠ (nb075_alpha_dummy_021) := by
  simpa only [nb075_alpha_dummy_019, nb075_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb075_distinct_025 : (nb075_alpha_dummy_020) ≠ (nb075_alpha_dummy_021) := by
  simpa only [nb075_alpha_dummy_020, nb075_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb075_fresh_026 (x : Var) : (nb075_alpha_dummy_022 x) ∉ (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb075_alpha_dummy_022] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb075_fresh_027 (x : Var) : (nb075_alpha_dummy_023 x) ∉ (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb075_alpha_dummy_023] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb075_fresh_028 (x : Var) : (nb075_alpha_dummy_024 x) ∉ (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb075_alpha_dummy_024] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb075_distinct_029 (x : Var) : (nb075_alpha_dummy_022 x) ≠ (nb075_alpha_dummy_023 x) := by
  simpa only [nb075_alpha_dummy_022, nb075_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb075_distinct_030 (x : Var) : (nb075_alpha_dummy_022 x) ≠ (nb075_alpha_dummy_024 x) := by
  simpa only [nb075_alpha_dummy_022, nb075_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb075_distinct_031 (x : Var) : (nb075_alpha_dummy_023 x) ≠ (nb075_alpha_dummy_024 x) := by
  simpa only [nb075_alpha_dummy_023, nb075_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb075_fresh_032 : (nb075_alpha_dummy_031) ∉ (((Class.cv (nb075_alpha_dummy_020))).fv ∪ ((Class.cv (nb075_alpha_dummy_020))).fv) := by
  simpa only [nb075_alpha_dummy_031] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_020))).fv ∪ ((Class.cv (nb075_alpha_dummy_020))).fv) 0

theorem nb075_fresh_033 : (nb075_alpha_dummy_027) ∉ (((Class.cv (nb075_alpha_dummy_020))).fv ∪ ((Class.cv (nb075_alpha_dummy_021))).fv) := by
  simpa only [nb075_alpha_dummy_027] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_020))).fv ∪ ((Class.cv (nb075_alpha_dummy_021))).fv) 0

theorem nb075_fresh_034 : (nb075_alpha_dummy_033) ∉ (((Class.cv (nb075_alpha_dummy_021))).fv ∪ ((Class.cv (nb075_alpha_dummy_021))).fv) := by
  simpa only [nb075_alpha_dummy_033] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_021))).fv ∪ ((Class.cv (nb075_alpha_dummy_021))).fv) 0

theorem nb075_fresh_035 (x : Var) : (nb075_alpha_dummy_032 x) ∉ (((Class.cv (nb075_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_023 x))).fv) := by
  simpa only [nb075_alpha_dummy_032] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_023 x))).fv) 0

theorem nb075_fresh_036 (x : Var) : (nb075_alpha_dummy_028 x) ∉ (((Class.cv (nb075_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_024 x))).fv) := by
  simpa only [nb075_alpha_dummy_028] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_024 x))).fv) 0

theorem nb075_fresh_037 (x : Var) : (nb075_alpha_dummy_034 x) ∉ (((Class.cv (nb075_alpha_dummy_024 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_024 x))).fv) := by
  simpa only [nb075_alpha_dummy_034] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_024 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_024 x))).fv) 0

theorem nb075_fresh_038 : (nb075_alpha_dummy_045) ∉ (((Class.cv (nb075_alpha_dummy_042))).fv ∪ ((Class.cv (nb075_alpha_dummy_041))).fv) := by
  simpa only [nb075_alpha_dummy_045] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_042))).fv ∪ ((Class.cv (nb075_alpha_dummy_041))).fv) 0

theorem nb075_fresh_039 : (nb075_alpha_dummy_046) ∉ (((Class.cv (nb075_alpha_dummy_042))).fv ∪ ((Class.cv (nb075_alpha_dummy_041))).fv) := by
  simpa only [nb075_alpha_dummy_046] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_042))).fv ∪ ((Class.cv (nb075_alpha_dummy_041))).fv) 1

theorem nb075_distinct_040 : (nb075_alpha_dummy_045) ≠ (nb075_alpha_dummy_046) := by
  simpa only [nb075_alpha_dummy_045, nb075_alpha_dummy_046] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_042))).fv ∪ ((Class.cv (nb075_alpha_dummy_041))).fv) (i := 0) (j := 1) (by decide))

theorem nb075_fresh_041 (x : Var) : (nb075_alpha_dummy_047 x) ∉ (((Class.cv (nb075_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_043 x))).fv) := by
  simpa only [nb075_alpha_dummy_047] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_043 x))).fv) 0

theorem nb075_fresh_042 (x : Var) : (nb075_alpha_dummy_048 x) ∉ (((Class.cv (nb075_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_043 x))).fv) := by
  simpa only [nb075_alpha_dummy_048] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_043 x))).fv) 1

theorem nb075_distinct_043 (x : Var) : (nb075_alpha_dummy_047 x) ≠ (nb075_alpha_dummy_048 x) := by
  simpa only [nb075_alpha_dummy_047, nb075_alpha_dummy_048] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_043 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb075_fresh_044 : (nb075_alpha_dummy_053) ∉ (((Class.cv (nb075_alpha_dummy_046))).fv) := by
  simpa only [nb075_alpha_dummy_053] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_046))).fv) 0

theorem nb075_fresh_045 : (nb075_alpha_dummy_054) ∉ (((Class.cv (nb075_alpha_dummy_046))).fv) := by
  simpa only [nb075_alpha_dummy_054] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_046))).fv) 1

theorem nb075_distinct_046 : (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_054) := by
  simpa only [nb075_alpha_dummy_053, nb075_alpha_dummy_054] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_046))).fv) (i := 0) (j := 1) (by decide))

theorem nb075_fresh_047 (x : Var) : (nb075_alpha_dummy_055 x) ∉ (((Class.cv (nb075_alpha_dummy_048 x))).fv) := by
  simpa only [nb075_alpha_dummy_055] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_048 x))).fv) 0

theorem nb075_fresh_048 (x : Var) : (nb075_alpha_dummy_056 x) ∉ (((Class.cv (nb075_alpha_dummy_048 x))).fv) := by
  simpa only [nb075_alpha_dummy_056] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_048 x))).fv) 1

theorem nb075_distinct_049 (x : Var) : (nb075_alpha_dummy_055 x) ≠ (nb075_alpha_dummy_056 x) := by
  simpa only [nb075_alpha_dummy_055, nb075_alpha_dummy_056] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_048 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb075_fresh_050 : (nb075_alpha_dummy_059) ∉ (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb075_alpha_dummy_059] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 0

theorem nb075_fresh_051 : (nb075_alpha_dummy_060) ∉ (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb075_alpha_dummy_060] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 1

theorem nb075_fresh_052 : (nb075_alpha_dummy_061) ∉ (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb075_alpha_dummy_061] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 2

theorem nb075_distinct_053 : (nb075_alpha_dummy_059) ≠ (nb075_alpha_dummy_060) := by
  simpa only [nb075_alpha_dummy_059, nb075_alpha_dummy_060] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb075_distinct_054 : (nb075_alpha_dummy_059) ≠ (nb075_alpha_dummy_061) := by
  simpa only [nb075_alpha_dummy_059, nb075_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb075_distinct_055 : (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_061) := by
  simpa only [nb075_alpha_dummy_060, nb075_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb075_fresh_056 (x : Var) : (nb075_alpha_dummy_062 x) ∉ (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb075_alpha_dummy_062] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb075_fresh_057 (x : Var) : (nb075_alpha_dummy_063 x) ∉ (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb075_alpha_dummy_063] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb075_fresh_058 (x : Var) : (nb075_alpha_dummy_064 x) ∉ (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb075_alpha_dummy_064] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb075_distinct_059 (x : Var) : (nb075_alpha_dummy_062 x) ≠ (nb075_alpha_dummy_063 x) := by
  simpa only [nb075_alpha_dummy_062, nb075_alpha_dummy_063] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb075_distinct_060 (x : Var) : (nb075_alpha_dummy_062 x) ≠ (nb075_alpha_dummy_064 x) := by
  simpa only [nb075_alpha_dummy_062, nb075_alpha_dummy_064] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb075_distinct_061 (x : Var) : (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_064 x) := by
  simpa only [nb075_alpha_dummy_063, nb075_alpha_dummy_064] using
    (freshVar_injective (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb075_fresh_062 : (nb075_alpha_dummy_071) ∉ (((Class.cv (nb075_alpha_dummy_060))).fv ∪ ((Class.cv (nb075_alpha_dummy_060))).fv) := by
  simpa only [nb075_alpha_dummy_071] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_060))).fv ∪ ((Class.cv (nb075_alpha_dummy_060))).fv) 0

theorem nb075_fresh_063 : (nb075_alpha_dummy_067) ∉ (((Class.cv (nb075_alpha_dummy_060))).fv ∪ ((Class.cv (nb075_alpha_dummy_061))).fv) := by
  simpa only [nb075_alpha_dummy_067] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_060))).fv ∪ ((Class.cv (nb075_alpha_dummy_061))).fv) 0

theorem nb075_fresh_064 : (nb075_alpha_dummy_073) ∉ (((Class.cv (nb075_alpha_dummy_061))).fv ∪ ((Class.cv (nb075_alpha_dummy_061))).fv) := by
  simpa only [nb075_alpha_dummy_073] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_061))).fv ∪ ((Class.cv (nb075_alpha_dummy_061))).fv) 0

theorem nb075_fresh_065 (x : Var) : (nb075_alpha_dummy_072 x) ∉ (((Class.cv (nb075_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_063 x))).fv) := by
  simpa only [nb075_alpha_dummy_072] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_063 x))).fv) 0

theorem nb075_fresh_066 (x : Var) : (nb075_alpha_dummy_068 x) ∉ (((Class.cv (nb075_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_064 x))).fv) := by
  simpa only [nb075_alpha_dummy_068] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_064 x))).fv) 0

theorem nb075_fresh_067 (x : Var) : (nb075_alpha_dummy_074 x) ∉ (((Class.cv (nb075_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_064 x))).fv) := by
  simpa only [nb075_alpha_dummy_074] using freshVar_not_mem (((Class.cv (nb075_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb075_alpha_dummy_064 x))).fv) 0

theorem nb075_fresh_068 (x : Var) : (nb075_alpha_dummy_007 x) ∉ (((Class.cv x)).fv ∪ ((Class.cv (nb075_alpha_dummy_002 x))).fv) := by
  simpa only [nb075_alpha_dummy_007] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb075_alpha_dummy_002 x))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
