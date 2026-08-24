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

noncomputable def nb051_alpha_dummy_000 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : Var := (freshVar (({x} : Finset Var) ∪ (A).fv ∪ ({y} : Finset Var) ∪ (B).fv ∪ (C).fv) 0)

noncomputable def nb051_alpha_dummy_001 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : Var := (freshVar (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb051_alpha_dummy_000 x y A B C)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (Wff.classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C))).fv) 0)

noncomputable def nb051_alpha_dummy_002 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) : Var := (freshVar (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (Wff.classEq (Class.cv z) C))).fv) 0)

noncomputable def nb051_alpha_dummy_003 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : Var := (freshVar (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb051_alpha_dummy_000 x y A B C))).fv) 0)

noncomputable def nb051_alpha_dummy_004 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : Var := (freshVar (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb051_alpha_dummy_000 x y A B C))).fv) 1)

noncomputable def nb051_alpha_dummy_005 (x : Var) (y : Var) (z : Var) : Var := (freshVar (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) 0)

noncomputable def nb051_alpha_dummy_006 (x : Var) (y : Var) (z : Var) : Var := (freshVar (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) 1)

noncomputable def nb051_alpha_dummy_007 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))))))).fv ∪ ((syn_ccompl (Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (Class.cv (nb051_alpha_dummy_000 x y A B C)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb051_alpha_dummy_008 (x : Var) (y : Var) (z : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))))))).fv ∪ ((syn_ccompl (Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb051_alpha_dummy_009 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : Var := (freshVar (((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))))).fv) 0)

noncomputable def nb051_alpha_dummy_010 (x : Var) (y : Var) (z : Var) : Var := (freshVar (((Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))))).fv) 0)

noncomputable def nb051_alpha_dummy_011 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : Var := (freshVar (((Class.cv (nb051_alpha_dummy_004 x y A B C))).fv) 0)

noncomputable def nb051_alpha_dummy_012 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : Var := (freshVar (((Class.cv (nb051_alpha_dummy_004 x y A B C))).fv) 1)

noncomputable def nb051_alpha_dummy_013 (x : Var) (y : Var) (z : Var) : Var := (freshVar (((Class.cv (nb051_alpha_dummy_006 x y z))).fv) 0)

noncomputable def nb051_alpha_dummy_014 (x : Var) (y : Var) (z : Var) : Var := (freshVar (((Class.cv (nb051_alpha_dummy_006 x y z))).fv) 1)

noncomputable def nb051_alpha_dummy_015 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb051_alpha_dummy_011 x y A B C)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb051_alpha_dummy_011 x y A B C)) (syn_c1c))).fv ∪ ((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv) 0)

noncomputable def nb051_alpha_dummy_016 (x : Var) (y : Var) (z : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb051_alpha_dummy_013 x y z)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb051_alpha_dummy_013 x y z)) (syn_c1c))).fv ∪ ((Class.cv (nb051_alpha_dummy_013 x y z))).fv) 0)

noncomputable def nb051_alpha_dummy_017 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : Var := (freshVar (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb051_alpha_dummy_018 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : Var := (freshVar (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb051_alpha_dummy_019 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : Var := (freshVar (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb051_alpha_dummy_020 (x : Var) (y : Var) (z : Var) : Var := (freshVar (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb051_alpha_dummy_021 (x : Var) (y : Var) (z : Var) : Var := (freshVar (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb051_alpha_dummy_022 (x : Var) (y : Var) (z : Var) : Var := (freshVar (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb051_alpha_dummy_023 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb051_alpha_dummy_018 x y A B C)) (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv ∪ ((syn_cnin (Class.cv (nb051_alpha_dummy_018 x y A B C)) (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv) 0)

noncomputable def nb051_alpha_dummy_024 (x : Var) (y : Var) (z : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb051_alpha_dummy_021 x y z)) (Class.cv (nb051_alpha_dummy_022 x y z)))).fv ∪ ((syn_cnin (Class.cv (nb051_alpha_dummy_021 x y z)) (Class.cv (nb051_alpha_dummy_022 x y z)))).fv) 0)

noncomputable def nb051_alpha_dummy_025 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : Var := (freshVar (((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv ∪ ((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv) 0)

noncomputable def nb051_alpha_dummy_026 (x : Var) (y : Var) (z : Var) : Var := (freshVar (((Class.cv (nb051_alpha_dummy_021 x y z))).fv ∪ ((Class.cv (nb051_alpha_dummy_022 x y z))).fv) 0)

noncomputable def nb051_alpha_dummy_027 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb051_alpha_dummy_018 x y A B C)))).fv ∪ ((syn_ccompl (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv) 0)

noncomputable def nb051_alpha_dummy_028 (x : Var) (y : Var) (z : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb051_alpha_dummy_021 x y z)))).fv ∪ ((syn_ccompl (Class.cv (nb051_alpha_dummy_022 x y z)))).fv) 0)

noncomputable def nb051_alpha_dummy_029 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : Var := (freshVar (((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv ∪ ((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv) 0)

noncomputable def nb051_alpha_dummy_030 (x : Var) (y : Var) (z : Var) : Var := (freshVar (((Class.cv (nb051_alpha_dummy_021 x y z))).fv ∪ ((Class.cv (nb051_alpha_dummy_021 x y z))).fv) 0)

noncomputable def nb051_alpha_dummy_031 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : Var := (freshVar (((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv ∪ ((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv) 0)

noncomputable def nb051_alpha_dummy_032 (x : Var) (y : Var) (z : Var) : Var := (freshVar (((Class.cv (nb051_alpha_dummy_022 x y z))).fv ∪ ((Class.cv (nb051_alpha_dummy_022 x y z))).fv) 0)

noncomputable def nb051_alpha_dummy_033 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : Var := (freshVar (((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (Class.cv (nb051_alpha_dummy_000 x y A B C)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (Class.cv (nb051_alpha_dummy_000 x y A B C)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb051_alpha_dummy_034 (x : Var) (y : Var) (z : Var) : Var := (freshVar (((Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb051_alpha_dummy_035 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb051_alpha_dummy_036 (x : Var) (y : Var) (z : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb051_alpha_dummy_037 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))).fv ∪ ((syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))).fv) 0)

noncomputable def nb051_alpha_dummy_038 (x : Var) (y : Var) (z : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))).fv ∪ ((syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
