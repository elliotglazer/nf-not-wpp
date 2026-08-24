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

noncomputable def nb072_alpha_dummy_000 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 0)

noncomputable def nb072_alpha_dummy_001 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 1)

noncomputable def nb072_alpha_dummy_002 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_003 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) 1)

noncomputable def nb072_alpha_dummy_004 (x : Var) (y : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

noncomputable def nb072_alpha_dummy_005 (x : Var) (y : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

noncomputable def nb072_alpha_dummy_006 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb072_alpha_dummy_007 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb072_alpha_dummy_008 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))))))).fv) 0)

noncomputable def nb072_alpha_dummy_009 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))))))).fv) 0)

noncomputable def nb072_alpha_dummy_010 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_003 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_011 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_003 A B R S_cls H))).fv) 1)

noncomputable def nb072_alpha_dummy_012 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_005 x y))).fv) 0)

noncomputable def nb072_alpha_dummy_013 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_005 x y))).fv) 1)

noncomputable def nb072_alpha_dummy_014 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb072_alpha_dummy_010 A B R S_cls H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_010 A B R S_cls H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_015 (x : Var) (y : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb072_alpha_dummy_012 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_012 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_012 x y))).fv) 0)

noncomputable def nb072_alpha_dummy_016 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb072_alpha_dummy_017 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb072_alpha_dummy_018 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb072_alpha_dummy_019 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb072_alpha_dummy_020 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb072_alpha_dummy_021 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb072_alpha_dummy_022 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb072_alpha_dummy_017 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_017 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv) 0)

noncomputable def nb072_alpha_dummy_023 (x : Var) (y : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb072_alpha_dummy_020 x y)) (Class.cv (nb072_alpha_dummy_021 x y)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_020 x y)) (Class.cv (nb072_alpha_dummy_021 x y)))).fv) 0)

noncomputable def nb072_alpha_dummy_024 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_025 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_020 x y))).fv ∪ ((Class.cv (nb072_alpha_dummy_021 x y))).fv) 0)

noncomputable def nb072_alpha_dummy_026 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb072_alpha_dummy_017 A B R S_cls H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_018 A B R S_cls H)))).fv) 0)

noncomputable def nb072_alpha_dummy_027 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb072_alpha_dummy_020 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_021 x y)))).fv) 0)

noncomputable def nb072_alpha_dummy_028 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_017 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_029 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_020 x y))).fv ∪ ((Class.cv (nb072_alpha_dummy_020 x y))).fv) 0)

noncomputable def nb072_alpha_dummy_030 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_018 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_031 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_021 x y))).fv ∪ ((Class.cv (nb072_alpha_dummy_021 x y))).fv) 0)

noncomputable def nb072_alpha_dummy_032 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb072_alpha_dummy_033 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb072_alpha_dummy_034 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb072_alpha_dummy_035 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb072_alpha_dummy_036 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))).fv) 0)

noncomputable def nb072_alpha_dummy_037 (x : Var) (y : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))).fv) 0)

noncomputable def nb072_alpha_dummy_038 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))).fv ∪ ((syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))).fv) 0)

noncomputable def nb072_alpha_dummy_039 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))).fv ∪ ((syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))).fv) 1)

noncomputable def nb072_alpha_dummy_040 (x : Var) (y : Var) (H : Class) : Var := (freshVar (((syn_cfv H (Class.cv x))).fv ∪ ((syn_cfv H (Class.cv y))).fv) 0)

noncomputable def nb072_alpha_dummy_041 (x : Var) (y : Var) (H : Class) : Var := (freshVar (((syn_cfv H (Class.cv x))).fv ∪ ((syn_cfv H (Class.cv y))).fv) 1)

noncomputable def nb072_alpha_dummy_042 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb072_alpha_dummy_043 (x : Var) (y : Var) (H : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb072_alpha_dummy_044 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))))).fv) 0)

noncomputable def nb072_alpha_dummy_045 (x : Var) (y : Var) (H : Class) : Var := (freshVar (((Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))))).fv) 0)

noncomputable def nb072_alpha_dummy_046 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar ((H).fv ∪ ((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_047 (x : Var) (H : Class) : Var := (freshVar ((H).fv ∪ ((Class.cv x)).fv) 0)

noncomputable def nb072_alpha_dummy_048 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (({(nb072_alpha_dummy_046 A B R S_cls H)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)))).fv) 0)

noncomputable def nb072_alpha_dummy_049 (x : Var) (H : Class) : Var := (freshVar (({(nb072_alpha_dummy_047 x H)} : Finset Var) ∪ ((syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H)))).fv) 0)

noncomputable def nb072_alpha_dummy_050 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cab (nb072_alpha_dummy_048 A B R S_cls H) (Wff.classEq (Class.cab (nb072_alpha_dummy_046 A B R S_cls H) (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)))) (syn_csn (Class.cv (nb072_alpha_dummy_048 A B R S_cls H)))))).fv) 0)

noncomputable def nb072_alpha_dummy_051 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cab (nb072_alpha_dummy_048 A B R S_cls H) (Wff.classEq (Class.cab (nb072_alpha_dummy_046 A B R S_cls H) (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)))) (syn_csn (Class.cv (nb072_alpha_dummy_048 A B R S_cls H)))))).fv) 1)

noncomputable def nb072_alpha_dummy_052 (x : Var) (H : Class) : Var := (freshVar (((Class.cab (nb072_alpha_dummy_049 x H) (Wff.classEq (Class.cab (nb072_alpha_dummy_047 x H) (syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H)))) (syn_csn (Class.cv (nb072_alpha_dummy_049 x H)))))).fv) 0)

noncomputable def nb072_alpha_dummy_053 (x : Var) (H : Class) : Var := (freshVar (((Class.cab (nb072_alpha_dummy_049 x H) (Wff.classEq (Class.cab (nb072_alpha_dummy_047 x H) (syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H)))) (syn_csn (Class.cv (nb072_alpha_dummy_049 x H)))))).fv) 1)

noncomputable def nb072_alpha_dummy_054 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_046 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_055 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_046 A B R S_cls H))).fv) 1)

noncomputable def nb072_alpha_dummy_056 (x : Var) (H : Class) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb072_alpha_dummy_047 x H))).fv) 0)

noncomputable def nb072_alpha_dummy_057 (x : Var) (H : Class) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb072_alpha_dummy_047 x H))).fv) 1)

noncomputable def nb072_alpha_dummy_058 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb072_alpha_dummy_059 (x : Var) (H : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb072_alpha_dummy_060 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))))).fv) 0)

noncomputable def nb072_alpha_dummy_061 (x : Var) (H : Class) : Var := (freshVar (((Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))))).fv) 0)

noncomputable def nb072_alpha_dummy_062 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_055 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_063 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_055 A B R S_cls H))).fv) 1)

noncomputable def nb072_alpha_dummy_064 (x : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_057 x H))).fv) 0)

noncomputable def nb072_alpha_dummy_065 (x : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_057 x H))).fv) 1)

noncomputable def nb072_alpha_dummy_066 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb072_alpha_dummy_062 A B R S_cls H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_062 A B R S_cls H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_067 (x : Var) (H : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb072_alpha_dummy_064 x H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_064 x H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_064 x H))).fv) 0)

noncomputable def nb072_alpha_dummy_068 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb072_alpha_dummy_069 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb072_alpha_dummy_070 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb072_alpha_dummy_071 (x : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb072_alpha_dummy_072 (x : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb072_alpha_dummy_073 (x : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb072_alpha_dummy_074 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb072_alpha_dummy_069 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_069 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv) 0)

noncomputable def nb072_alpha_dummy_075 (x : Var) (H : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb072_alpha_dummy_072 x H)) (Class.cv (nb072_alpha_dummy_073 x H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_072 x H)) (Class.cv (nb072_alpha_dummy_073 x H)))).fv) 0)

noncomputable def nb072_alpha_dummy_076 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_077 (x : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_072 x H))).fv ∪ ((Class.cv (nb072_alpha_dummy_073 x H))).fv) 0)

noncomputable def nb072_alpha_dummy_078 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb072_alpha_dummy_069 A B R S_cls H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv) 0)

noncomputable def nb072_alpha_dummy_079 (x : Var) (H : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb072_alpha_dummy_072 x H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_073 x H)))).fv) 0)

noncomputable def nb072_alpha_dummy_080 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_081 (x : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_072 x H))).fv ∪ ((Class.cv (nb072_alpha_dummy_072 x H))).fv) 0)

noncomputable def nb072_alpha_dummy_082 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_083 (x : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_073 x H))).fv ∪ ((Class.cv (nb072_alpha_dummy_073 x H))).fv) 0)

noncomputable def nb072_alpha_dummy_084 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb072_alpha_dummy_085 (x : Var) (H : Class) : Var := (freshVar (((Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb072_alpha_dummy_086 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb072_alpha_dummy_087 (x : Var) (H : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb072_alpha_dummy_088 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))).fv) 0)

noncomputable def nb072_alpha_dummy_089 (x : Var) (H : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))).fv) 0)

noncomputable def nb072_alpha_dummy_090 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_048 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_091 (x : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_049 x H))).fv) 0)

noncomputable def nb072_alpha_dummy_092 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_039 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_093 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_039 A B R S_cls H))).fv) 1)

noncomputable def nb072_alpha_dummy_094 (x : Var) (y : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_041 x y H))).fv) 0)

noncomputable def nb072_alpha_dummy_095 (x : Var) (y : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_041 x y H))).fv) 1)

noncomputable def nb072_alpha_dummy_096 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb072_alpha_dummy_092 A B R S_cls H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_092 A B R S_cls H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_097 (x : Var) (y : Var) (H : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb072_alpha_dummy_094 x y H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_094 x y H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_094 x y H))).fv) 0)

noncomputable def nb072_alpha_dummy_098 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb072_alpha_dummy_099 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb072_alpha_dummy_100 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb072_alpha_dummy_101 (x : Var) (y : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb072_alpha_dummy_102 (x : Var) (y : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb072_alpha_dummy_103 (x : Var) (y : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb072_alpha_dummy_104 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb072_alpha_dummy_099 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_099 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv) 0)

noncomputable def nb072_alpha_dummy_105 (x : Var) (y : Var) (H : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb072_alpha_dummy_102 x y H)) (Class.cv (nb072_alpha_dummy_103 x y H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_102 x y H)) (Class.cv (nb072_alpha_dummy_103 x y H)))).fv) 0)

noncomputable def nb072_alpha_dummy_106 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_107 (x : Var) (y : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_102 x y H))).fv ∪ ((Class.cv (nb072_alpha_dummy_103 x y H))).fv) 0)

noncomputable def nb072_alpha_dummy_108 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb072_alpha_dummy_099 A B R S_cls H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv) 0)

noncomputable def nb072_alpha_dummy_109 (x : Var) (y : Var) (H : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb072_alpha_dummy_102 x y H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_103 x y H)))).fv) 0)

noncomputable def nb072_alpha_dummy_110 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_111 (x : Var) (y : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_102 x y H))).fv ∪ ((Class.cv (nb072_alpha_dummy_102 x y H))).fv) 0)

noncomputable def nb072_alpha_dummy_112 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_113 (x : Var) (y : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_103 x y H))).fv ∪ ((Class.cv (nb072_alpha_dummy_103 x y H))).fv) 0)

noncomputable def nb072_alpha_dummy_114 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb072_alpha_dummy_115 (x : Var) (y : Var) (H : Class) : Var := (freshVar (((Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb072_alpha_dummy_116 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar ((H).fv ∪ ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_117 (y : Var) (H : Class) : Var := (freshVar ((H).fv ∪ ((Class.cv y)).fv) 0)

noncomputable def nb072_alpha_dummy_118 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (({(nb072_alpha_dummy_116 A B R S_cls H)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)))).fv) 0)

noncomputable def nb072_alpha_dummy_119 (y : Var) (H : Class) : Var := (freshVar (({(nb072_alpha_dummy_117 y H)} : Finset Var) ∪ ((syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H)))).fv) 0)

noncomputable def nb072_alpha_dummy_120 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cab (nb072_alpha_dummy_118 A B R S_cls H) (Wff.classEq (Class.cab (nb072_alpha_dummy_116 A B R S_cls H) (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)))) (syn_csn (Class.cv (nb072_alpha_dummy_118 A B R S_cls H)))))).fv) 0)

noncomputable def nb072_alpha_dummy_121 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cab (nb072_alpha_dummy_118 A B R S_cls H) (Wff.classEq (Class.cab (nb072_alpha_dummy_116 A B R S_cls H) (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)))) (syn_csn (Class.cv (nb072_alpha_dummy_118 A B R S_cls H)))))).fv) 1)

noncomputable def nb072_alpha_dummy_122 (y : Var) (H : Class) : Var := (freshVar (((Class.cab (nb072_alpha_dummy_119 y H) (Wff.classEq (Class.cab (nb072_alpha_dummy_117 y H) (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H)))) (syn_csn (Class.cv (nb072_alpha_dummy_119 y H)))))).fv) 0)

noncomputable def nb072_alpha_dummy_123 (y : Var) (H : Class) : Var := (freshVar (((Class.cab (nb072_alpha_dummy_119 y H) (Wff.classEq (Class.cab (nb072_alpha_dummy_117 y H) (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H)))) (syn_csn (Class.cv (nb072_alpha_dummy_119 y H)))))).fv) 1)

noncomputable def nb072_alpha_dummy_124 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_116 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_125 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_116 A B R S_cls H))).fv) 1)

noncomputable def nb072_alpha_dummy_126 (y : Var) (H : Class) : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv (nb072_alpha_dummy_117 y H))).fv) 0)

noncomputable def nb072_alpha_dummy_127 (y : Var) (H : Class) : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv (nb072_alpha_dummy_117 y H))).fv) 1)

noncomputable def nb072_alpha_dummy_128 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb072_alpha_dummy_124 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_124 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H) (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb072_alpha_dummy_129 (y : Var) (H : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb072_alpha_dummy_126 y H) (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_126 y H) (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv (nb072_alpha_dummy_117 y H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb072_alpha_dummy_130 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cab (nb072_alpha_dummy_124 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_124 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))))).fv) 0)

noncomputable def nb072_alpha_dummy_131 (y : Var) (H : Class) : Var := (freshVar (((Class.cab (nb072_alpha_dummy_126 y H) (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_126 y H) (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))))).fv) 0)

noncomputable def nb072_alpha_dummy_132 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_125 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_133 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_125 A B R S_cls H))).fv) 1)

noncomputable def nb072_alpha_dummy_134 (y : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_127 y H))).fv) 0)

noncomputable def nb072_alpha_dummy_135 (y : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_127 y H))).fv) 1)

noncomputable def nb072_alpha_dummy_136 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb072_alpha_dummy_132 A B R S_cls H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_132 A B R S_cls H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_137 (y : Var) (H : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb072_alpha_dummy_134 y H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_134 y H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_134 y H))).fv) 0)

noncomputable def nb072_alpha_dummy_138 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb072_alpha_dummy_139 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb072_alpha_dummy_140 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb072_alpha_dummy_141 (y : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb072_alpha_dummy_142 (y : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb072_alpha_dummy_143 (y : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb072_alpha_dummy_144 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb072_alpha_dummy_139 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_139 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv) 0)

noncomputable def nb072_alpha_dummy_145 (y : Var) (H : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb072_alpha_dummy_142 y H)) (Class.cv (nb072_alpha_dummy_143 y H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_142 y H)) (Class.cv (nb072_alpha_dummy_143 y H)))).fv) 0)

noncomputable def nb072_alpha_dummy_146 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_139 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_140 A B R S_cls H))).fv) 0)

noncomputable def nb072_alpha_dummy_147 (y : Var) (H : Class) : Var := (freshVar (((Class.cv (nb072_alpha_dummy_142 y H))).fv ∪ ((Class.cv (nb072_alpha_dummy_143 y H))).fv) 0)

noncomputable def nb072_alpha_dummy_148 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb072_alpha_dummy_139 A B R S_cls H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv) 0)

noncomputable def nb072_alpha_dummy_149 (y : Var) (H : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb072_alpha_dummy_142 y H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_143 y H)))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
