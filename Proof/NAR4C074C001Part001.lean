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

noncomputable def nb074_alpha_dummy_000 : Var := (freshVar ((∅ : Finset Var)) 0)

noncomputable def nb074_alpha_dummy_001 : Var := (freshVar (({(nb074_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cdm (Class.cv (nb074_alpha_dummy_000)))).fv) 0)

noncomputable def nb074_alpha_dummy_002 (x : Var) : Var := (freshVar (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cdm (Class.cv x))).fv) 0)

noncomputable def nb074_alpha_dummy_003 : Var := (freshVar (({(nb074_alpha_dummy_000)} : Finset Var) ∪ ({(nb074_alpha_dummy_001)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb074_alpha_dummy_000)) (syn_cvv)) (Wff.classEq (Class.cv (nb074_alpha_dummy_001)) (syn_cdm (Class.cv (nb074_alpha_dummy_000)))))).fv) 0)

noncomputable def nb074_alpha_dummy_004 (x : Var) : Var := (freshVar (({x} : Finset Var) ∪ ({(nb074_alpha_dummy_002 x)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classEq (Class.cv (nb074_alpha_dummy_002 x)) (syn_cdm (Class.cv x))))).fv) 0)

noncomputable def nb074_alpha_dummy_005 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_000))).fv ∪ ((Class.cv (nb074_alpha_dummy_001))).fv) 0)

noncomputable def nb074_alpha_dummy_006 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_000))).fv ∪ ((Class.cv (nb074_alpha_dummy_001))).fv) 1)

noncomputable def nb074_alpha_dummy_007 (x : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb074_alpha_dummy_002 x))).fv) 0)

noncomputable def nb074_alpha_dummy_008 (x : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb074_alpha_dummy_002 x))).fv) 1)

noncomputable def nb074_alpha_dummy_009 : Var := (freshVar (((syn_ccompl (Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cphi (Class.cv (nb074_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb074_alpha_dummy_010 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb074_alpha_dummy_011 : Var := (freshVar (((Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cphi (Class.cv (nb074_alpha_dummy_006))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_000)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cphi (Class.cv (nb074_alpha_dummy_006))))))).fv) 0)

noncomputable def nb074_alpha_dummy_012 (x : Var) : Var := (freshVar (((Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv x) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))))))).fv) 0)

noncomputable def nb074_alpha_dummy_013 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_006))).fv) 0)

noncomputable def nb074_alpha_dummy_014 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_006))).fv) 1)

noncomputable def nb074_alpha_dummy_015 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_008 x))).fv) 0)

noncomputable def nb074_alpha_dummy_016 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_008 x))).fv) 1)

noncomputable def nb074_alpha_dummy_017 : Var := (freshVar (((Wff.classMem (Class.cv (nb074_alpha_dummy_013)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_013)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_013))).fv) 0)

noncomputable def nb074_alpha_dummy_018 (x : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb074_alpha_dummy_015 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_015 x)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_015 x))).fv) 0)

noncomputable def nb074_alpha_dummy_019 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb074_alpha_dummy_020 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb074_alpha_dummy_021 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb074_alpha_dummy_022 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb074_alpha_dummy_023 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb074_alpha_dummy_024 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb074_alpha_dummy_025 : Var := (freshVar (((syn_cnin (Class.cv (nb074_alpha_dummy_020)) (Class.cv (nb074_alpha_dummy_021)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_020)) (Class.cv (nb074_alpha_dummy_021)))).fv) 0)

noncomputable def nb074_alpha_dummy_026 (x : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb074_alpha_dummy_023 x)) (Class.cv (nb074_alpha_dummy_024 x)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_023 x)) (Class.cv (nb074_alpha_dummy_024 x)))).fv) 0)

noncomputable def nb074_alpha_dummy_027 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_020))).fv ∪ ((Class.cv (nb074_alpha_dummy_021))).fv) 0)

noncomputable def nb074_alpha_dummy_028 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_024 x))).fv) 0)

noncomputable def nb074_alpha_dummy_029 : Var := (freshVar (((syn_ccompl (Class.cv (nb074_alpha_dummy_020)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_021)))).fv) 0)

noncomputable def nb074_alpha_dummy_030 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb074_alpha_dummy_023 x)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_024 x)))).fv) 0)

noncomputable def nb074_alpha_dummy_031 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_020))).fv ∪ ((Class.cv (nb074_alpha_dummy_020))).fv) 0)

noncomputable def nb074_alpha_dummy_032 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_023 x))).fv) 0)

noncomputable def nb074_alpha_dummy_033 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_021))).fv ∪ ((Class.cv (nb074_alpha_dummy_021))).fv) 0)

noncomputable def nb074_alpha_dummy_034 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_024 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_024 x))).fv) 0)

noncomputable def nb074_alpha_dummy_035 : Var := (freshVar (((Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb074_alpha_dummy_036 (x : Var) : Var := (freshVar (((Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb074_alpha_dummy_037 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_006))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb074_alpha_dummy_038 (x : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb074_alpha_dummy_039 : Var := (freshVar (((syn_cphi (Class.cv (nb074_alpha_dummy_006)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_006)))).fv) 0)

noncomputable def nb074_alpha_dummy_040 (x : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))).fv) 0)

noncomputable def nb074_alpha_dummy_041 : Var := (freshVar (((syn_ccnv (Class.cv (nb074_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb074_alpha_dummy_042 : Var := (freshVar (((syn_ccnv (Class.cv (nb074_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb074_alpha_dummy_043 (x : Var) : Var := (freshVar (((syn_ccnv (Class.cv x))).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb074_alpha_dummy_044 (x : Var) : Var := (freshVar (((syn_ccnv (Class.cv x))).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb074_alpha_dummy_045 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_042))).fv ∪ ((Class.cv (nb074_alpha_dummy_041))).fv) 0)

noncomputable def nb074_alpha_dummy_046 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_042))).fv ∪ ((Class.cv (nb074_alpha_dummy_041))).fv) 1)

noncomputable def nb074_alpha_dummy_047 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_043 x))).fv) 0)

noncomputable def nb074_alpha_dummy_048 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_044 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_043 x))).fv) 1)

noncomputable def nb074_alpha_dummy_049 : Var := (freshVar (((syn_ccompl (Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cphi (Class.cv (nb074_alpha_dummy_046)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb074_alpha_dummy_050 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb074_alpha_dummy_051 : Var := (freshVar (((Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cphi (Class.cv (nb074_alpha_dummy_046))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cphi (Class.cv (nb074_alpha_dummy_046))))))).fv) 0)

noncomputable def nb074_alpha_dummy_052 (x : Var) : Var := (freshVar (((Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))))))).fv) 0)

noncomputable def nb074_alpha_dummy_053 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_046))).fv) 0)

noncomputable def nb074_alpha_dummy_054 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_046))).fv) 1)

noncomputable def nb074_alpha_dummy_055 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_048 x))).fv) 0)

noncomputable def nb074_alpha_dummy_056 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_048 x))).fv) 1)

noncomputable def nb074_alpha_dummy_057 : Var := (freshVar (((Wff.classMem (Class.cv (nb074_alpha_dummy_053)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_053)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_053))).fv) 0)

noncomputable def nb074_alpha_dummy_058 (x : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb074_alpha_dummy_055 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_055 x)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_055 x))).fv) 0)

noncomputable def nb074_alpha_dummy_059 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb074_alpha_dummy_060 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb074_alpha_dummy_061 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb074_alpha_dummy_062 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb074_alpha_dummy_063 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb074_alpha_dummy_064 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb074_alpha_dummy_065 : Var := (freshVar (((syn_cnin (Class.cv (nb074_alpha_dummy_060)) (Class.cv (nb074_alpha_dummy_061)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_060)) (Class.cv (nb074_alpha_dummy_061)))).fv) 0)

noncomputable def nb074_alpha_dummy_066 (x : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb074_alpha_dummy_063 x)) (Class.cv (nb074_alpha_dummy_064 x)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_063 x)) (Class.cv (nb074_alpha_dummy_064 x)))).fv) 0)

noncomputable def nb074_alpha_dummy_067 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_060))).fv ∪ ((Class.cv (nb074_alpha_dummy_061))).fv) 0)

noncomputable def nb074_alpha_dummy_068 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_064 x))).fv) 0)

noncomputable def nb074_alpha_dummy_069 : Var := (freshVar (((syn_ccompl (Class.cv (nb074_alpha_dummy_060)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_061)))).fv) 0)

noncomputable def nb074_alpha_dummy_070 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb074_alpha_dummy_063 x)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_064 x)))).fv) 0)

noncomputable def nb074_alpha_dummy_071 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_060))).fv ∪ ((Class.cv (nb074_alpha_dummy_060))).fv) 0)

noncomputable def nb074_alpha_dummy_072 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_063 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_063 x))).fv) 0)

noncomputable def nb074_alpha_dummy_073 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_061))).fv ∪ ((Class.cv (nb074_alpha_dummy_061))).fv) 0)

noncomputable def nb074_alpha_dummy_074 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_064 x))).fv) 0)

noncomputable def nb074_alpha_dummy_075 : Var := (freshVar (((Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb074_alpha_dummy_076 (x : Var) : Var := (freshVar (((Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb074_alpha_dummy_077 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_046))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb074_alpha_dummy_078 (x : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb074_alpha_dummy_079 : Var := (freshVar (((syn_cphi (Class.cv (nb074_alpha_dummy_046)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_046)))).fv) 0)

noncomputable def nb074_alpha_dummy_080 (x : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))).fv) 0)

noncomputable def nb074_alpha_dummy_081 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_000))).fv) 0)

noncomputable def nb074_alpha_dummy_082 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_000))).fv) 1)

noncomputable def nb074_alpha_dummy_083 (x : Var) : Var := (freshVar (((Class.cv x)).fv) 0)

noncomputable def nb074_alpha_dummy_084 (x : Var) : Var := (freshVar (((Class.cv x)).fv) 1)

noncomputable def nb074_alpha_dummy_085 : Var := (freshVar (({(nb074_alpha_dummy_081)} : Finset Var) ∪ ({(nb074_alpha_dummy_082)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb074_alpha_dummy_082)) (Class.cv (nb074_alpha_dummy_000)) (Class.cv (nb074_alpha_dummy_081)))).fv) 0)

noncomputable def nb074_alpha_dummy_086 (x : Var) : Var := (freshVar (({(nb074_alpha_dummy_083 x)} : Finset Var) ∪ ({(nb074_alpha_dummy_084 x)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb074_alpha_dummy_084 x)) (Class.cv x) (Class.cv (nb074_alpha_dummy_083 x)))).fv) 0)

noncomputable def nb074_alpha_dummy_087 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_081))).fv ∪ ((Class.cv (nb074_alpha_dummy_082))).fv) 0)

noncomputable def nb074_alpha_dummy_088 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_081))).fv ∪ ((Class.cv (nb074_alpha_dummy_082))).fv) 1)

noncomputable def nb074_alpha_dummy_089 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_083 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_084 x))).fv) 0)

noncomputable def nb074_alpha_dummy_090 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_083 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_084 x))).fv) 1)

noncomputable def nb074_alpha_dummy_091 : Var := (freshVar (((syn_ccompl (Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cphi (Class.cv (nb074_alpha_dummy_088)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb074_alpha_dummy_092 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb074_alpha_dummy_093 : Var := (freshVar (((Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cphi (Class.cv (nb074_alpha_dummy_088))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cphi (Class.cv (nb074_alpha_dummy_088))))))).fv) 0)

noncomputable def nb074_alpha_dummy_094 (x : Var) : Var := (freshVar (((Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))))).fv) 0)

noncomputable def nb074_alpha_dummy_095 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_088))).fv) 0)

noncomputable def nb074_alpha_dummy_096 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_088))).fv) 1)

noncomputable def nb074_alpha_dummy_097 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_090 x))).fv) 0)

noncomputable def nb074_alpha_dummy_098 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_090 x))).fv) 1)

noncomputable def nb074_alpha_dummy_099 : Var := (freshVar (((Wff.classMem (Class.cv (nb074_alpha_dummy_095)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_095)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_095))).fv) 0)

noncomputable def nb074_alpha_dummy_100 (x : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb074_alpha_dummy_097 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_097 x)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_097 x))).fv) 0)

noncomputable def nb074_alpha_dummy_101 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb074_alpha_dummy_102 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb074_alpha_dummy_103 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb074_alpha_dummy_104 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb074_alpha_dummy_105 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb074_alpha_dummy_106 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb074_alpha_dummy_107 : Var := (freshVar (((syn_cnin (Class.cv (nb074_alpha_dummy_102)) (Class.cv (nb074_alpha_dummy_103)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_102)) (Class.cv (nb074_alpha_dummy_103)))).fv) 0)

noncomputable def nb074_alpha_dummy_108 (x : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb074_alpha_dummy_105 x)) (Class.cv (nb074_alpha_dummy_106 x)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_105 x)) (Class.cv (nb074_alpha_dummy_106 x)))).fv) 0)

noncomputable def nb074_alpha_dummy_109 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_102))).fv ∪ ((Class.cv (nb074_alpha_dummy_103))).fv) 0)

noncomputable def nb074_alpha_dummy_110 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_105 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_106 x))).fv) 0)

noncomputable def nb074_alpha_dummy_111 : Var := (freshVar (((syn_ccompl (Class.cv (nb074_alpha_dummy_102)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_103)))).fv) 0)

noncomputable def nb074_alpha_dummy_112 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb074_alpha_dummy_105 x)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_106 x)))).fv) 0)

noncomputable def nb074_alpha_dummy_113 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_102))).fv ∪ ((Class.cv (nb074_alpha_dummy_102))).fv) 0)

noncomputable def nb074_alpha_dummy_114 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_105 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_105 x))).fv) 0)

noncomputable def nb074_alpha_dummy_115 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_103))).fv ∪ ((Class.cv (nb074_alpha_dummy_103))).fv) 0)

noncomputable def nb074_alpha_dummy_116 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_106 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_106 x))).fv) 0)

noncomputable def nb074_alpha_dummy_117 : Var := (freshVar (((Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb074_alpha_dummy_118 (x : Var) : Var := (freshVar (((Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb074_alpha_dummy_119 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_088))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb074_alpha_dummy_120 (x : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb074_alpha_dummy_121 : Var := (freshVar (((syn_cphi (Class.cv (nb074_alpha_dummy_088)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_088)))).fv) 0)

noncomputable def nb074_alpha_dummy_122 (x : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))).fv) 0)

noncomputable def nb074_alpha_dummy_123 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_082))).fv ∪ ((Class.cv (nb074_alpha_dummy_081))).fv) 0)

noncomputable def nb074_alpha_dummy_124 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_082))).fv ∪ ((Class.cv (nb074_alpha_dummy_081))).fv) 1)

noncomputable def nb074_alpha_dummy_125 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_084 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_083 x))).fv) 0)

noncomputable def nb074_alpha_dummy_126 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_084 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_083 x))).fv) 1)

noncomputable def nb074_alpha_dummy_127 : Var := (freshVar (((syn_ccompl (Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cphi (Class.cv (nb074_alpha_dummy_124)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb074_alpha_dummy_128 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb074_alpha_dummy_129 : Var := (freshVar (((Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cphi (Class.cv (nb074_alpha_dummy_124))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cphi (Class.cv (nb074_alpha_dummy_124))))))).fv) 0)

noncomputable def nb074_alpha_dummy_130 (x : Var) : Var := (freshVar (((Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))))).fv) 0)

noncomputable def nb074_alpha_dummy_131 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_124))).fv) 0)

noncomputable def nb074_alpha_dummy_132 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_124))).fv) 1)

noncomputable def nb074_alpha_dummy_133 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_126 x))).fv) 0)

noncomputable def nb074_alpha_dummy_134 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_126 x))).fv) 1)

noncomputable def nb074_alpha_dummy_135 : Var := (freshVar (((Wff.classMem (Class.cv (nb074_alpha_dummy_131)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_131)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_131))).fv) 0)

noncomputable def nb074_alpha_dummy_136 (x : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb074_alpha_dummy_133 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_133 x)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_133 x))).fv) 0)

noncomputable def nb074_alpha_dummy_137 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb074_alpha_dummy_138 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb074_alpha_dummy_139 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb074_alpha_dummy_140 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb074_alpha_dummy_141 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb074_alpha_dummy_142 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb074_alpha_dummy_143 : Var := (freshVar (((syn_cnin (Class.cv (nb074_alpha_dummy_138)) (Class.cv (nb074_alpha_dummy_139)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_138)) (Class.cv (nb074_alpha_dummy_139)))).fv) 0)

noncomputable def nb074_alpha_dummy_144 (x : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb074_alpha_dummy_141 x)) (Class.cv (nb074_alpha_dummy_142 x)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_141 x)) (Class.cv (nb074_alpha_dummy_142 x)))).fv) 0)

noncomputable def nb074_alpha_dummy_145 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_138))).fv ∪ ((Class.cv (nb074_alpha_dummy_139))).fv) 0)

noncomputable def nb074_alpha_dummy_146 (x : Var) : Var := (freshVar (((Class.cv (nb074_alpha_dummy_141 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_142 x))).fv) 0)

noncomputable def nb074_alpha_dummy_147 : Var := (freshVar (((syn_ccompl (Class.cv (nb074_alpha_dummy_138)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_139)))).fv) 0)

noncomputable def nb074_alpha_dummy_148 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb074_alpha_dummy_141 x)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_142 x)))).fv) 0)

noncomputable def nb074_alpha_dummy_149 : Var := (freshVar (((Class.cv (nb074_alpha_dummy_138))).fv ∪ ((Class.cv (nb074_alpha_dummy_138))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
