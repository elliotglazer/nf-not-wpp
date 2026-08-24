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

noncomputable def nb077_alpha_dummy_000 (F : Class) (I : Class) : Var := (freshVar ((F).fv ∪ (I).fv) 0)

noncomputable def nb077_alpha_dummy_001 (F : Class) (I : Class) : Var := (freshVar (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv) 0)

noncomputable def nb077_alpha_dummy_002 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv) 0)

noncomputable def nb077_alpha_dummy_003 (F : Class) (I : Class) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_001 F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I)))))).fv) 0)

noncomputable def nb077_alpha_dummy_004 (F : Class) (I : Class) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_001 F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I)))))).fv) 1)

noncomputable def nb077_alpha_dummy_005 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_002 x F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I))) (Class.cv (nb077_alpha_dummy_002 x F I)))))).fv) 0)

noncomputable def nb077_alpha_dummy_006 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_002 x F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I))) (Class.cv (nb077_alpha_dummy_002 x F I)))))).fv) 1)

noncomputable def nb077_alpha_dummy_007 (F : Class) (I : Class) : Var := (freshVar (((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪ ((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_008 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪ ((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_009 (F : Class) (I : Class) : Var := (freshVar (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_010 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) 0)

noncomputable def nb077_alpha_dummy_011 (F : Class) (I : Class) : Var := (freshVar (((syn_cnin (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪ ((syn_cnin (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_012 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((syn_cnin (syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I))) (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪ ((syn_cnin (syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I))) (Class.cv (nb077_alpha_dummy_002 x F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_013 (F : Class) (I : Class) : Var := (freshVar (((syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_014 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) 0)

noncomputable def nb077_alpha_dummy_015 (F : Class) (I : Class) : Var := (freshVar (((syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_016 (F : Class) (I : Class) : Var := (freshVar (((syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) 1)

noncomputable def nb077_alpha_dummy_017 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) 0)

noncomputable def nb077_alpha_dummy_018 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) 1)

noncomputable def nb077_alpha_dummy_019 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_015 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_020 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_015 F I))).fv) 1)

noncomputable def nb077_alpha_dummy_021 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_017 x F I))).fv) 0)

noncomputable def nb077_alpha_dummy_022 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_017 x F I))).fv) 1)

noncomputable def nb077_alpha_dummy_023 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb077_alpha_dummy_024 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_018 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_017 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb077_alpha_dummy_025 (F : Class) (I : Class) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))))).fv) 0)

noncomputable def nb077_alpha_dummy_026 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_018 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_018 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))))).fv) 0)

noncomputable def nb077_alpha_dummy_027 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_020 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_028 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_020 F I))).fv) 1)

noncomputable def nb077_alpha_dummy_029 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) 0)

noncomputable def nb077_alpha_dummy_030 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) 1)

noncomputable def nb077_alpha_dummy_031 (F : Class) (I : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_027 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_027 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_027 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_032 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_029 x F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_029 x F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_029 x F I))).fv) 0)

noncomputable def nb077_alpha_dummy_033 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb077_alpha_dummy_034 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb077_alpha_dummy_035 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb077_alpha_dummy_036 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb077_alpha_dummy_037 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb077_alpha_dummy_038 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb077_alpha_dummy_039 (F : Class) (I : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_034 F I)) (Class.cv (nb077_alpha_dummy_035 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_034 F I)) (Class.cv (nb077_alpha_dummy_035 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_040 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_037 x F I)) (Class.cv (nb077_alpha_dummy_038 x F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_037 x F I)) (Class.cv (nb077_alpha_dummy_038 x F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_041 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_034 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_035 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_042 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_037 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_038 x F I))).fv) 0)

noncomputable def nb077_alpha_dummy_043 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_034 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_035 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_044 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_037 x F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_038 x F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_045 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_034 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_034 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_046 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_037 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_037 x F I))).fv) 0)

noncomputable def nb077_alpha_dummy_047 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_035 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_035 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_048 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_038 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_038 x F I))).fv) 0)

noncomputable def nb077_alpha_dummy_049 (F : Class) (I : Class) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb077_alpha_dummy_050 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_017 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_017 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb077_alpha_dummy_051 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb077_alpha_dummy_052 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb077_alpha_dummy_053 (F : Class) (I : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_054 (x : Var) (F : Class) (I : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_055 (F : Class) (I : Class) : Var := (freshVar (((syn_cnin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))) (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))) (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv) 0)

noncomputable def nb077_alpha_dummy_056 (x : Var) (F : Class) : Var := (freshVar (((syn_cnin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))) (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))) (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv) 0)

noncomputable def nb077_alpha_dummy_057 (F : Class) (I : Class) : Var := (freshVar (((syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st)))).fv ∪ ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv) 0)

noncomputable def nb077_alpha_dummy_058 (x : Var) (F : Class) : Var := (freshVar (((syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st)))).fv ∪ ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv) 0)

noncomputable def nb077_alpha_dummy_059 (F : Class) (I : Class) : Var := (freshVar (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv) 0)

noncomputable def nb077_alpha_dummy_060 (F : Class) (I : Class) : Var := (freshVar (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv) 1)

noncomputable def nb077_alpha_dummy_061 (F : Class) (I : Class) : Var := (freshVar (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv) 2)

noncomputable def nb077_alpha_dummy_062 (x : Var) : Var := (freshVar (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv) 0)

noncomputable def nb077_alpha_dummy_063 (x : Var) : Var := (freshVar (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv) 1)

noncomputable def nb077_alpha_dummy_064 (x : Var) : Var := (freshVar (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv) 2)

noncomputable def nb077_alpha_dummy_065 (F : Class) (I : Class) : Var := (freshVar (({(nb077_alpha_dummy_059 F I)} : Finset Var) ∪ ({(nb077_alpha_dummy_060 F I)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_061 F I) (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_059 F I)) (syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st)) (Class.cv (nb077_alpha_dummy_061 F I))) (syn_wbr (Class.cv (nb077_alpha_dummy_061 F I)) (syn_ccnv (syn_c1st)) (Class.cv (nb077_alpha_dummy_060 F I)))))).fv) 0)

noncomputable def nb077_alpha_dummy_066 (x : Var) : Var := (freshVar (({(nb077_alpha_dummy_062 x)} : Finset Var) ∪ ({(nb077_alpha_dummy_063 x)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_064 x) (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_062 x)) (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st)) (Class.cv (nb077_alpha_dummy_064 x))) (syn_wbr (Class.cv (nb077_alpha_dummy_064 x)) (syn_ccnv (syn_c1st)) (Class.cv (nb077_alpha_dummy_063 x)))))).fv) 0)

noncomputable def nb077_alpha_dummy_067 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_060 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_068 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_060 F I))).fv) 1)

noncomputable def nb077_alpha_dummy_069 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) 0)

noncomputable def nb077_alpha_dummy_070 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) 1)

noncomputable def nb077_alpha_dummy_071 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb077_alpha_dummy_072 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb077_alpha_dummy_073 (F : Class) (I : Class) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))))).fv) 0)

noncomputable def nb077_alpha_dummy_074 (x : Var) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))))).fv) 0)

noncomputable def nb077_alpha_dummy_075 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_068 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_076 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_068 F I))).fv) 1)

noncomputable def nb077_alpha_dummy_077 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_070 x))).fv) 0)

noncomputable def nb077_alpha_dummy_078 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_070 x))).fv) 1)

noncomputable def nb077_alpha_dummy_079 (F : Class) (I : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_075 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_075 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_075 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_080 (x : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_077 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_077 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_077 x))).fv) 0)

noncomputable def nb077_alpha_dummy_081 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb077_alpha_dummy_082 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb077_alpha_dummy_083 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb077_alpha_dummy_084 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb077_alpha_dummy_085 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb077_alpha_dummy_086 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb077_alpha_dummy_087 (F : Class) (I : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_082 F I)) (Class.cv (nb077_alpha_dummy_083 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_082 F I)) (Class.cv (nb077_alpha_dummy_083 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_088 (x : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_085 x)) (Class.cv (nb077_alpha_dummy_086 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_085 x)) (Class.cv (nb077_alpha_dummy_086 x)))).fv) 0)

noncomputable def nb077_alpha_dummy_089 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_082 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_083 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_090 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_085 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_086 x))).fv) 0)

noncomputable def nb077_alpha_dummy_091 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_082 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_083 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_092 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_085 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_086 x)))).fv) 0)

noncomputable def nb077_alpha_dummy_093 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_082 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_082 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_094 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_085 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_085 x))).fv) 0)

noncomputable def nb077_alpha_dummy_095 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_083 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_083 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_096 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_086 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_086 x))).fv) 0)

noncomputable def nb077_alpha_dummy_097 (F : Class) (I : Class) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb077_alpha_dummy_098 (x : Var) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb077_alpha_dummy_099 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb077_alpha_dummy_100 (x : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb077_alpha_dummy_101 (F : Class) (I : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_102 (x : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))).fv) 0)

noncomputable def nb077_alpha_dummy_103 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_061 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_104 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_061 F I))).fv) 1)

noncomputable def nb077_alpha_dummy_105 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_064 x))).fv) 0)

noncomputable def nb077_alpha_dummy_106 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_064 x))).fv) 1)

noncomputable def nb077_alpha_dummy_107 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb077_alpha_dummy_108 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb077_alpha_dummy_109 (F : Class) (I : Class) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))))).fv) 0)

noncomputable def nb077_alpha_dummy_110 (x : Var) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))))).fv) 0)

noncomputable def nb077_alpha_dummy_111 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_104 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_112 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_104 F I))).fv) 1)

noncomputable def nb077_alpha_dummy_113 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_106 x))).fv) 0)

noncomputable def nb077_alpha_dummy_114 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_106 x))).fv) 1)

noncomputable def nb077_alpha_dummy_115 (F : Class) (I : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_111 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_111 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_111 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_116 (x : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_113 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_113 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_113 x))).fv) 0)

noncomputable def nb077_alpha_dummy_117 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb077_alpha_dummy_118 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb077_alpha_dummy_119 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb077_alpha_dummy_120 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb077_alpha_dummy_121 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb077_alpha_dummy_122 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb077_alpha_dummy_123 (F : Class) (I : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_118 F I)) (Class.cv (nb077_alpha_dummy_119 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_118 F I)) (Class.cv (nb077_alpha_dummy_119 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_124 (x : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_121 x)) (Class.cv (nb077_alpha_dummy_122 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_121 x)) (Class.cv (nb077_alpha_dummy_122 x)))).fv) 0)

noncomputable def nb077_alpha_dummy_125 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_118 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_119 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_126 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_121 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_122 x))).fv) 0)

noncomputable def nb077_alpha_dummy_127 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_118 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_119 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_128 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_121 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_122 x)))).fv) 0)

noncomputable def nb077_alpha_dummy_129 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_118 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_118 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_130 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_121 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_121 x))).fv) 0)

noncomputable def nb077_alpha_dummy_131 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_119 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_119 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_132 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_122 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_122 x))).fv) 0)

noncomputable def nb077_alpha_dummy_133 (F : Class) (I : Class) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb077_alpha_dummy_134 (x : Var) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb077_alpha_dummy_135 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb077_alpha_dummy_136 (x : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb077_alpha_dummy_137 (F : Class) (I : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_138 (x : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))).fv) 0)

noncomputable def nb077_alpha_dummy_139 (F : Class) (I : Class) : Var := (freshVar (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) 0)

noncomputable def nb077_alpha_dummy_140 (F : Class) (I : Class) : Var := (freshVar (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) 1)

noncomputable def nb077_alpha_dummy_141 (F : Class) (I : Class) : Var := (freshVar (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) 2)

noncomputable def nb077_alpha_dummy_142 (x : Var) : Var := (freshVar (((syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) 0)

noncomputable def nb077_alpha_dummy_143 (x : Var) : Var := (freshVar (((syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) 1)

noncomputable def nb077_alpha_dummy_144 (x : Var) : Var := (freshVar (((syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) 2)

noncomputable def nb077_alpha_dummy_145 (F : Class) (I : Class) : Var := (freshVar (({(nb077_alpha_dummy_139 F I)} : Finset Var) ∪ ({(nb077_alpha_dummy_140 F I)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_141 F I) (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_139 F I)) (syn_c1st) (Class.cv (nb077_alpha_dummy_141 F I))) (syn_wbr (Class.cv (nb077_alpha_dummy_141 F I)) (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (Class.cv (nb077_alpha_dummy_140 F I)))))).fv) 0)

noncomputable def nb077_alpha_dummy_146 (x : Var) : Var := (freshVar (({(nb077_alpha_dummy_142 x)} : Finset Var) ∪ ({(nb077_alpha_dummy_143 x)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_144 x) (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_142 x)) (syn_c1st) (Class.cv (nb077_alpha_dummy_144 x))) (syn_wbr (Class.cv (nb077_alpha_dummy_144 x)) (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (Class.cv (nb077_alpha_dummy_143 x)))))).fv) 0)

noncomputable def nb077_alpha_dummy_147 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_140 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_148 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_140 F I))).fv) 1)

noncomputable def nb077_alpha_dummy_149 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
