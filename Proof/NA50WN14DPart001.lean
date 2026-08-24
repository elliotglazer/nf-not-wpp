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

noncomputable def nb050_alpha_dummy_000 (x : Var) (A : Class) (B : Class) : Var := (freshVar (({x} : Finset Var) ∪ (A).fv ∪ (B).fv) 0)

noncomputable def nb050_alpha_dummy_001 (x : Var) (A : Class) (B : Class) : Var := (freshVar (({x} : Finset Var) ∪ ({(nb050_alpha_dummy_000 x A B)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classEq (Class.cv (nb050_alpha_dummy_000 x A B)) B))).fv) 0)

noncomputable def nb050_alpha_dummy_002 (x : Var) (y : Var) (A : Class) (B : Class) : Var := (freshVar (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classEq (Class.cv y) B))).fv) 0)

noncomputable def nb050_alpha_dummy_003 (x : Var) (A : Class) (B : Class) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb050_alpha_dummy_000 x A B))).fv) 0)

noncomputable def nb050_alpha_dummy_004 (x : Var) (A : Class) (B : Class) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb050_alpha_dummy_000 x A B))).fv) 1)

noncomputable def nb050_alpha_dummy_005 (x : Var) (y : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

noncomputable def nb050_alpha_dummy_006 (x : Var) (y : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

noncomputable def nb050_alpha_dummy_007 (x : Var) (A : Class) (B : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb050_alpha_dummy_003 x A B) (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv x) (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B)) (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))))))).fv ∪ ((syn_ccompl (Class.cab (nb050_alpha_dummy_003 x A B) (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv (nb050_alpha_dummy_000 x A B)) (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B)) (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb050_alpha_dummy_008 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb050_alpha_dummy_005 x y) (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv x) (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y)) (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb050_alpha_dummy_005 x y) (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv y) (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y)) (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb050_alpha_dummy_009 (x : Var) (A : Class) (B : Class) : Var := (freshVar (((Class.cab (nb050_alpha_dummy_003 x A B) (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv x) (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B)) (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))))))).fv ∪ ((Class.cab (nb050_alpha_dummy_003 x A B) (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv x) (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B)) (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))))))).fv) 0)

noncomputable def nb050_alpha_dummy_010 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb050_alpha_dummy_005 x y) (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv x) (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y)) (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))))))).fv ∪ ((Class.cab (nb050_alpha_dummy_005 x y) (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv x) (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y)) (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))))))).fv) 0)

noncomputable def nb050_alpha_dummy_011 (x : Var) (A : Class) (B : Class) : Var := (freshVar (((Class.cv (nb050_alpha_dummy_004 x A B))).fv) 0)

noncomputable def nb050_alpha_dummy_012 (x : Var) (A : Class) (B : Class) : Var := (freshVar (((Class.cv (nb050_alpha_dummy_004 x A B))).fv) 1)

noncomputable def nb050_alpha_dummy_013 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb050_alpha_dummy_006 x y))).fv) 0)

noncomputable def nb050_alpha_dummy_014 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb050_alpha_dummy_006 x y))).fv) 1)

noncomputable def nb050_alpha_dummy_015 (x : Var) (A : Class) (B : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb050_alpha_dummy_011 x A B)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb050_alpha_dummy_011 x A B)) (syn_c1c))).fv ∪ ((Class.cv (nb050_alpha_dummy_011 x A B))).fv) 0)

noncomputable def nb050_alpha_dummy_016 (x : Var) (y : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb050_alpha_dummy_013 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb050_alpha_dummy_013 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb050_alpha_dummy_013 x y))).fv) 0)

noncomputable def nb050_alpha_dummy_017 (x : Var) (A : Class) (B : Class) : Var := (freshVar (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb050_alpha_dummy_018 (x : Var) (A : Class) (B : Class) : Var := (freshVar (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb050_alpha_dummy_019 (x : Var) (A : Class) (B : Class) : Var := (freshVar (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb050_alpha_dummy_020 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb050_alpha_dummy_021 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb050_alpha_dummy_022 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb050_alpha_dummy_023 (x : Var) (A : Class) (B : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb050_alpha_dummy_018 x A B)) (Class.cv (nb050_alpha_dummy_019 x A B)))).fv ∪ ((syn_cnin (Class.cv (nb050_alpha_dummy_018 x A B)) (Class.cv (nb050_alpha_dummy_019 x A B)))).fv) 0)

noncomputable def nb050_alpha_dummy_024 (x : Var) (y : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb050_alpha_dummy_021 x y)) (Class.cv (nb050_alpha_dummy_022 x y)))).fv ∪ ((syn_cnin (Class.cv (nb050_alpha_dummy_021 x y)) (Class.cv (nb050_alpha_dummy_022 x y)))).fv) 0)

noncomputable def nb050_alpha_dummy_025 (x : Var) (A : Class) (B : Class) : Var := (freshVar (((Class.cv (nb050_alpha_dummy_018 x A B))).fv ∪ ((Class.cv (nb050_alpha_dummy_019 x A B))).fv) 0)

noncomputable def nb050_alpha_dummy_026 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb050_alpha_dummy_021 x y))).fv ∪ ((Class.cv (nb050_alpha_dummy_022 x y))).fv) 0)

noncomputable def nb050_alpha_dummy_027 (x : Var) (A : Class) (B : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb050_alpha_dummy_018 x A B)))).fv ∪ ((syn_ccompl (Class.cv (nb050_alpha_dummy_019 x A B)))).fv) 0)

noncomputable def nb050_alpha_dummy_028 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb050_alpha_dummy_021 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb050_alpha_dummy_022 x y)))).fv) 0)

noncomputable def nb050_alpha_dummy_029 (x : Var) (A : Class) (B : Class) : Var := (freshVar (((Class.cv (nb050_alpha_dummy_018 x A B))).fv ∪ ((Class.cv (nb050_alpha_dummy_018 x A B))).fv) 0)

noncomputable def nb050_alpha_dummy_030 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb050_alpha_dummy_021 x y))).fv ∪ ((Class.cv (nb050_alpha_dummy_021 x y))).fv) 0)

noncomputable def nb050_alpha_dummy_031 (x : Var) (A : Class) (B : Class) : Var := (freshVar (((Class.cv (nb050_alpha_dummy_019 x A B))).fv ∪ ((Class.cv (nb050_alpha_dummy_019 x A B))).fv) 0)

noncomputable def nb050_alpha_dummy_032 (x : Var) (y : Var) : Var := (freshVar (((Class.cv (nb050_alpha_dummy_022 x y))).fv ∪ ((Class.cv (nb050_alpha_dummy_022 x y))).fv) 0)

noncomputable def nb050_alpha_dummy_033 (x : Var) (A : Class) (B : Class) : Var := (freshVar (((Class.cab (nb050_alpha_dummy_003 x A B) (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv (nb050_alpha_dummy_000 x A B)) (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B)) (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb050_alpha_dummy_003 x A B) (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv (nb050_alpha_dummy_000 x A B)) (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B)) (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb050_alpha_dummy_034 (x : Var) (y : Var) : Var := (freshVar (((Class.cab (nb050_alpha_dummy_005 x y) (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv y) (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y)) (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb050_alpha_dummy_005 x y) (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv y) (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y)) (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb050_alpha_dummy_035 (x : Var) (A : Class) (B : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb050_alpha_dummy_036 (x : Var) (y : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb050_alpha_dummy_037 (x : Var) (A : Class) (B : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))).fv ∪ ((syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))).fv) 0)

noncomputable def nb050_alpha_dummy_038 (x : Var) (y : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))).fv ∪ ((syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
