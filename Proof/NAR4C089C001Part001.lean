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

noncomputable def nb089_alpha_dummy_000 (A : Class) (B : Class) (R : Class) : Var := (freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0)

noncomputable def nb089_alpha_dummy_001 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_wbr R (syn_cwe) A)).fv ∪ ((syn_cmpt (nb089_alpha_dummy_000 A B R) (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R))))).fv ∪ ((syn_c0)).fv) 0)

noncomputable def nb089_alpha_dummy_002 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_wbr R (syn_cwe) A)).fv ∪ ((syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (Class.cv u)))).fv ∪ ((syn_c0)).fv) 0)

noncomputable def nb089_alpha_dummy_003 (A : Class) (B : Class) (R : Class) : Var := (freshVar (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv ∪ ((syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))).fv) 0)

noncomputable def nb089_alpha_dummy_004 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (({u} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv ∪ ((syn_cfdrowfib R A B (Class.cv u))).fv) 0)

noncomputable def nb089_alpha_dummy_005 (A : Class) (B : Class) (R : Class) : Var := (freshVar (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪ ({(nb089_alpha_dummy_003 A B R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb089_alpha_dummy_000 A B R)) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) (Wff.classEq (Class.cv (nb089_alpha_dummy_003 A B R)) (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))))).fv) 0)

noncomputable def nb089_alpha_dummy_006 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (({u} : Finset Var) ∪ ({(nb089_alpha_dummy_004 u A B R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) (Wff.classEq (Class.cv (nb089_alpha_dummy_004 u A B R)) (syn_cfdrowfib R A B (Class.cv u))))).fv) 0)

noncomputable def nb089_alpha_dummy_007 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_000 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_003 A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_008 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_000 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_003 A B R))).fv) 1)

noncomputable def nb089_alpha_dummy_009 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv u)).fv ∪ ((Class.cv (nb089_alpha_dummy_004 u A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_010 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv u)).fv ∪ ((Class.cv (nb089_alpha_dummy_004 u A B R))).fv) 1)

noncomputable def nb089_alpha_dummy_011 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_003 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb089_alpha_dummy_012 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv (nb089_alpha_dummy_004 u A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb089_alpha_dummy_013 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))))))).fv) 0)

noncomputable def nb089_alpha_dummy_014 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))))))).fv) 0)

noncomputable def nb089_alpha_dummy_015 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_008 A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_016 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_008 A B R))).fv) 1)

noncomputable def nb089_alpha_dummy_017 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_010 u A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_018 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_010 u A B R))).fv) 1)

noncomputable def nb089_alpha_dummy_019 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb089_alpha_dummy_015 A B R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb089_alpha_dummy_015 A B R)) (syn_c1c))).fv ∪ ((Class.cv (nb089_alpha_dummy_015 A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_020 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb089_alpha_dummy_017 u A B R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb089_alpha_dummy_017 u A B R)) (syn_c1c))).fv ∪ ((Class.cv (nb089_alpha_dummy_017 u A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_021 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb089_alpha_dummy_022 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb089_alpha_dummy_023 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb089_alpha_dummy_024 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb089_alpha_dummy_025 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb089_alpha_dummy_026 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb089_alpha_dummy_027 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb089_alpha_dummy_022 A B R)) (Class.cv (nb089_alpha_dummy_023 A B R)))).fv ∪ ((syn_cnin (Class.cv (nb089_alpha_dummy_022 A B R)) (Class.cv (nb089_alpha_dummy_023 A B R)))).fv) 0)

noncomputable def nb089_alpha_dummy_028 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb089_alpha_dummy_025 u A B R)) (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv ∪ ((syn_cnin (Class.cv (nb089_alpha_dummy_025 u A B R)) (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv) 0)

noncomputable def nb089_alpha_dummy_029 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_022 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_023 A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_030 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_025 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_026 u A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_031 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb089_alpha_dummy_022 A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb089_alpha_dummy_023 A B R)))).fv) 0)

noncomputable def nb089_alpha_dummy_032 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb089_alpha_dummy_025 u A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv) 0)

noncomputable def nb089_alpha_dummy_033 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_022 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_022 A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_034 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_025 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_025 u A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_035 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_023 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_023 A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_036 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_026 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_026 u A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_037 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_003 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_003 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb089_alpha_dummy_038 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv (nb089_alpha_dummy_004 u A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv (nb089_alpha_dummy_004 u A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb089_alpha_dummy_039 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb089_alpha_dummy_040 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb089_alpha_dummy_041 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))).fv ∪ ((syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))).fv) 0)

noncomputable def nb089_alpha_dummy_042 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))).fv ∪ ((syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))).fv) 0)

noncomputable def nb089_alpha_dummy_043 (A : Class) (B : Class) (R : Class) : Var := (freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_044 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) 0)

noncomputable def nb089_alpha_dummy_045 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))).fv ∪ ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_046 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))).fv ∪ ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) 1)

noncomputable def nb089_alpha_dummy_047 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))).fv ∪ ((Class.cv u)).fv) 0)

noncomputable def nb089_alpha_dummy_048 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))).fv ∪ ((Class.cv u)).fv) 1)

noncomputable def nb089_alpha_dummy_049 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb089_alpha_dummy_050 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb089_alpha_dummy_051 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))))).fv) 0)

noncomputable def nb089_alpha_dummy_052 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))))).fv) 0)

noncomputable def nb089_alpha_dummy_053 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_043 A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_054 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_044 u A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_055 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_046 A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_056 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_046 A B R))).fv) 1)

noncomputable def nb089_alpha_dummy_057 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_048 u A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_058 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_048 u A B R))).fv) 1)

noncomputable def nb089_alpha_dummy_059 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb089_alpha_dummy_055 A B R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb089_alpha_dummy_055 A B R)) (syn_c1c))).fv ∪ ((Class.cv (nb089_alpha_dummy_055 A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_060 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb089_alpha_dummy_057 u A B R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb089_alpha_dummy_057 u A B R)) (syn_c1c))).fv ∪ ((Class.cv (nb089_alpha_dummy_057 u A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_061 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb089_alpha_dummy_062 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb089_alpha_dummy_063 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb089_alpha_dummy_064 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb089_alpha_dummy_065 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb089_alpha_dummy_066 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb089_alpha_dummy_067 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb089_alpha_dummy_062 A B R)) (Class.cv (nb089_alpha_dummy_063 A B R)))).fv ∪ ((syn_cnin (Class.cv (nb089_alpha_dummy_062 A B R)) (Class.cv (nb089_alpha_dummy_063 A B R)))).fv) 0)

noncomputable def nb089_alpha_dummy_068 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb089_alpha_dummy_065 u A B R)) (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv ∪ ((syn_cnin (Class.cv (nb089_alpha_dummy_065 u A B R)) (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv) 0)

noncomputable def nb089_alpha_dummy_069 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_062 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_063 A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_070 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_065 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_066 u A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_071 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb089_alpha_dummy_062 A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb089_alpha_dummy_063 A B R)))).fv) 0)

noncomputable def nb089_alpha_dummy_072 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb089_alpha_dummy_065 u A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv) 0)

noncomputable def nb089_alpha_dummy_073 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_062 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_062 A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_074 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_065 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_065 u A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_075 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_063 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_063 A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_076 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb089_alpha_dummy_066 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_066 u A B R))).fv) 0)

noncomputable def nb089_alpha_dummy_077 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb089_alpha_dummy_078 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb089_alpha_dummy_079 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb089_alpha_dummy_080 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb089_alpha_dummy_081 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))).fv ∪ ((syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))).fv) 0)

noncomputable def nb089_alpha_dummy_082 (u : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))).fv ∪ ((syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))).fv) 0)

theorem nb089_fresh_000 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_013 A B R) ∉ (((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))))))).fv) := by
  simpa only [nb089_alpha_dummy_013] using freshVar_not_mem (((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))))))).fv) 0

theorem nb089_fresh_001 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_037 A B R) ∉ (((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_003 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_003 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb089_alpha_dummy_037] using freshVar_not_mem (((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_003 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_003 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb089_fresh_002 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_038 u A B R) ∉ (((Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv (nb089_alpha_dummy_004 u A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv (nb089_alpha_dummy_004 u A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb089_alpha_dummy_038] using freshVar_not_mem (((Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv (nb089_alpha_dummy_004 u A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv (nb089_alpha_dummy_004 u A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb089_fresh_003 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_014 u A B R) ∉ (((Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))))))).fv) := by
  simpa only [nb089_alpha_dummy_014] using freshVar_not_mem (((Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))))))).fv) 0

theorem nb089_fresh_004 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_077 A B R) ∉ (((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb089_alpha_dummy_077] using freshVar_not_mem (((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb089_fresh_005 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_051 A B R) ∉ (((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))))).fv) := by
  simpa only [nb089_alpha_dummy_051] using freshVar_not_mem (((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))))).fv) 0

theorem nb089_fresh_006 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_078 u A B R) ∉ (((Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb089_alpha_dummy_078] using freshVar_not_mem (((Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb089_fresh_007 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_052 u A B R) ∉ (((Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))))).fv) := by
  simpa only [nb089_alpha_dummy_052] using freshVar_not_mem (((Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))))).fv) 0

theorem nb089_fresh_008 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_007 A B R) ∉ (((Class.cv (nb089_alpha_dummy_000 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_003 A B R))).fv) := by
  simpa only [nb089_alpha_dummy_007] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_000 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_003 A B R))).fv) 0

theorem nb089_fresh_009 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_008 A B R) ∉ (((Class.cv (nb089_alpha_dummy_000 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_003 A B R))).fv) := by
  simpa only [nb089_alpha_dummy_008] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_000 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_003 A B R))).fv) 1

theorem nb089_distinct_010 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_007 A B R) ≠ (nb089_alpha_dummy_008 A B R) := by
  simpa only [nb089_alpha_dummy_007, nb089_alpha_dummy_008] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_000 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_003 A B R))).fv) (i := 0) (j := 1) (by decide))

theorem nb089_fresh_011 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_015 A B R) ∉ (((Class.cv (nb089_alpha_dummy_008 A B R))).fv) := by
  simpa only [nb089_alpha_dummy_015] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_008 A B R))).fv) 0

theorem nb089_fresh_012 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_016 A B R) ∉ (((Class.cv (nb089_alpha_dummy_008 A B R))).fv) := by
  simpa only [nb089_alpha_dummy_016] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_008 A B R))).fv) 1

theorem nb089_distinct_013 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_015 A B R) ≠ (nb089_alpha_dummy_016 A B R) := by
  simpa only [nb089_alpha_dummy_015, nb089_alpha_dummy_016] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_008 A B R))).fv) (i := 0) (j := 1) (by decide))

theorem nb089_fresh_014 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_017 u A B R) ∉ (((Class.cv (nb089_alpha_dummy_010 u A B R))).fv) := by
  simpa only [nb089_alpha_dummy_017] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_010 u A B R))).fv) 0

theorem nb089_fresh_015 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_018 u A B R) ∉ (((Class.cv (nb089_alpha_dummy_010 u A B R))).fv) := by
  simpa only [nb089_alpha_dummy_018] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_010 u A B R))).fv) 1

theorem nb089_distinct_016 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_017 u A B R) ≠ (nb089_alpha_dummy_018 u A B R) := by
  simpa only [nb089_alpha_dummy_017, nb089_alpha_dummy_018] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_010 u A B R))).fv) (i := 0) (j := 1) (by decide))

theorem nb089_fresh_017 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_021 A B R) ∉ (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb089_alpha_dummy_021] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb089_fresh_018 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_022 A B R) ∉ (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb089_alpha_dummy_022] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb089_fresh_019 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_023 A B R) ∉ (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb089_alpha_dummy_023] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb089_distinct_020 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_021 A B R) ≠ (nb089_alpha_dummy_022 A B R) := by
  simpa only [nb089_alpha_dummy_021, nb089_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb089_distinct_021 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_021 A B R) ≠ (nb089_alpha_dummy_023 A B R) := by
  simpa only [nb089_alpha_dummy_021, nb089_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb089_distinct_022 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_022 A B R) ≠ (nb089_alpha_dummy_023 A B R) := by
  simpa only [nb089_alpha_dummy_022, nb089_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb089_fresh_023 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_024 u A B R) ∉ (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb089_alpha_dummy_024] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb089_fresh_024 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_025 u A B R) ∉ (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb089_alpha_dummy_025] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb089_fresh_025 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_026 u A B R) ∉ (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb089_alpha_dummy_026] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb089_distinct_026 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_024 u A B R) ≠ (nb089_alpha_dummy_025 u A B R) := by
  simpa only [nb089_alpha_dummy_024, nb089_alpha_dummy_025] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb089_distinct_027 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_024 u A B R) ≠ (nb089_alpha_dummy_026 u A B R) := by
  simpa only [nb089_alpha_dummy_024, nb089_alpha_dummy_026] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb089_distinct_028 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_026 u A B R) := by
  simpa only [nb089_alpha_dummy_025, nb089_alpha_dummy_026] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb089_fresh_029 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_033 A B R) ∉ (((Class.cv (nb089_alpha_dummy_022 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_022 A B R))).fv) := by
  simpa only [nb089_alpha_dummy_033] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_022 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_022 A B R))).fv) 0

theorem nb089_fresh_030 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_029 A B R) ∉ (((Class.cv (nb089_alpha_dummy_022 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_023 A B R))).fv) := by
  simpa only [nb089_alpha_dummy_029] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_022 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_023 A B R))).fv) 0

theorem nb089_fresh_031 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_035 A B R) ∉ (((Class.cv (nb089_alpha_dummy_023 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_023 A B R))).fv) := by
  simpa only [nb089_alpha_dummy_035] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_023 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_023 A B R))).fv) 0

theorem nb089_fresh_032 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_034 u A B R) ∉ (((Class.cv (nb089_alpha_dummy_025 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_025 u A B R))).fv) := by
  simpa only [nb089_alpha_dummy_034] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_025 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_025 u A B R))).fv) 0

theorem nb089_fresh_033 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_030 u A B R) ∉ (((Class.cv (nb089_alpha_dummy_025 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_026 u A B R))).fv) := by
  simpa only [nb089_alpha_dummy_030] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_025 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_026 u A B R))).fv) 0

theorem nb089_fresh_034 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_036 u A B R) ∉ (((Class.cv (nb089_alpha_dummy_026 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_026 u A B R))).fv) := by
  simpa only [nb089_alpha_dummy_036] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_026 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_026 u A B R))).fv) 0

theorem nb089_fresh_035 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_053 A B R) ∉ (((Class.cv (nb089_alpha_dummy_043 A B R))).fv) := by
  simpa only [nb089_alpha_dummy_053] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_043 A B R))).fv) 0

theorem nb089_fresh_036 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_054 u A B R) ∉ (((Class.cv (nb089_alpha_dummy_044 u A B R))).fv) := by
  simpa only [nb089_alpha_dummy_054] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_044 u A B R))).fv) 0

theorem nb089_fresh_037 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_055 A B R) ∉ (((Class.cv (nb089_alpha_dummy_046 A B R))).fv) := by
  simpa only [nb089_alpha_dummy_055] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_046 A B R))).fv) 0

theorem nb089_fresh_038 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_056 A B R) ∉ (((Class.cv (nb089_alpha_dummy_046 A B R))).fv) := by
  simpa only [nb089_alpha_dummy_056] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_046 A B R))).fv) 1

theorem nb089_distinct_039 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_055 A B R) ≠ (nb089_alpha_dummy_056 A B R) := by
  simpa only [nb089_alpha_dummy_055, nb089_alpha_dummy_056] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_046 A B R))).fv) (i := 0) (j := 1) (by decide))

theorem nb089_fresh_040 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_057 u A B R) ∉ (((Class.cv (nb089_alpha_dummy_048 u A B R))).fv) := by
  simpa only [nb089_alpha_dummy_057] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_048 u A B R))).fv) 0

theorem nb089_fresh_041 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_058 u A B R) ∉ (((Class.cv (nb089_alpha_dummy_048 u A B R))).fv) := by
  simpa only [nb089_alpha_dummy_058] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_048 u A B R))).fv) 1

theorem nb089_distinct_042 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_057 u A B R) ≠ (nb089_alpha_dummy_058 u A B R) := by
  simpa only [nb089_alpha_dummy_057, nb089_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_048 u A B R))).fv) (i := 0) (j := 1) (by decide))

theorem nb089_fresh_043 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_061 A B R) ∉ (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb089_alpha_dummy_061] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb089_fresh_044 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_062 A B R) ∉ (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb089_alpha_dummy_062] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb089_fresh_045 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_063 A B R) ∉ (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb089_alpha_dummy_063] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb089_distinct_046 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_061 A B R) ≠ (nb089_alpha_dummy_062 A B R) := by
  simpa only [nb089_alpha_dummy_061, nb089_alpha_dummy_062] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb089_distinct_047 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_061 A B R) ≠ (nb089_alpha_dummy_063 A B R) := by
  simpa only [nb089_alpha_dummy_061, nb089_alpha_dummy_063] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb089_distinct_048 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_062 A B R) ≠ (nb089_alpha_dummy_063 A B R) := by
  simpa only [nb089_alpha_dummy_062, nb089_alpha_dummy_063] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb089_fresh_049 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_064 u A B R) ∉ (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb089_alpha_dummy_064] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb089_fresh_050 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_065 u A B R) ∉ (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb089_alpha_dummy_065] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb089_fresh_051 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_066 u A B R) ∉ (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb089_alpha_dummy_066] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb089_distinct_052 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_064 u A B R) ≠ (nb089_alpha_dummy_065 u A B R) := by
  simpa only [nb089_alpha_dummy_064, nb089_alpha_dummy_065] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb089_distinct_053 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_064 u A B R) ≠ (nb089_alpha_dummy_066 u A B R) := by
  simpa only [nb089_alpha_dummy_064, nb089_alpha_dummy_066] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb089_distinct_054 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_066 u A B R) := by
  simpa only [nb089_alpha_dummy_065, nb089_alpha_dummy_066] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb089_fresh_055 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_073 A B R) ∉ (((Class.cv (nb089_alpha_dummy_062 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_062 A B R))).fv) := by
  simpa only [nb089_alpha_dummy_073] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_062 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_062 A B R))).fv) 0

theorem nb089_fresh_056 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_069 A B R) ∉ (((Class.cv (nb089_alpha_dummy_062 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_063 A B R))).fv) := by
  simpa only [nb089_alpha_dummy_069] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_062 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_063 A B R))).fv) 0

theorem nb089_fresh_057 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_075 A B R) ∉ (((Class.cv (nb089_alpha_dummy_063 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_063 A B R))).fv) := by
  simpa only [nb089_alpha_dummy_075] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_063 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_063 A B R))).fv) 0

theorem nb089_fresh_058 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_074 u A B R) ∉ (((Class.cv (nb089_alpha_dummy_065 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_065 u A B R))).fv) := by
  simpa only [nb089_alpha_dummy_074] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_065 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_065 u A B R))).fv) 0

theorem nb089_fresh_059 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_070 u A B R) ∉ (((Class.cv (nb089_alpha_dummy_065 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_066 u A B R))).fv) := by
  simpa only [nb089_alpha_dummy_070] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_065 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_066 u A B R))).fv) 0

theorem nb089_fresh_060 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_076 u A B R) ∉ (((Class.cv (nb089_alpha_dummy_066 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_066 u A B R))).fv) := by
  simpa only [nb089_alpha_dummy_076] using freshVar_not_mem (((Class.cv (nb089_alpha_dummy_066 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_066 u A B R))).fv) 0

theorem nb089_fresh_061 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_009 u A B R) ∉ (((Class.cv u)).fv ∪ ((Class.cv (nb089_alpha_dummy_004 u A B R))).fv) := by
  simpa only [nb089_alpha_dummy_009] using freshVar_not_mem (((Class.cv u)).fv ∪ ((Class.cv (nb089_alpha_dummy_004 u A B R))).fv) 0

theorem nb089_fresh_062 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_010 u A B R) ∉ (((Class.cv u)).fv ∪ ((Class.cv (nb089_alpha_dummy_004 u A B R))).fv) := by
  simpa only [nb089_alpha_dummy_010] using freshVar_not_mem (((Class.cv u)).fv ∪ ((Class.cv (nb089_alpha_dummy_004 u A B R))).fv) 1

theorem nb089_distinct_063 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_009 u A B R) ≠ (nb089_alpha_dummy_010 u A B R) := by
  simpa only [nb089_alpha_dummy_009, nb089_alpha_dummy_010] using
    (freshVar_injective (((Class.cv u)).fv ∪ ((Class.cv (nb089_alpha_dummy_004 u A B R))).fv) (i := 0) (j := 1) (by decide))

theorem nb089_fresh_064 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_019 A B R) ∉ (((Wff.classMem (Class.cv (nb089_alpha_dummy_015 A B R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb089_alpha_dummy_015 A B R)) (syn_c1c))).fv ∪ ((Class.cv (nb089_alpha_dummy_015 A B R))).fv) := by
  simpa only [nb089_alpha_dummy_019] using freshVar_not_mem (((Wff.classMem (Class.cv (nb089_alpha_dummy_015 A B R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb089_alpha_dummy_015 A B R)) (syn_c1c))).fv ∪ ((Class.cv (nb089_alpha_dummy_015 A B R))).fv) 0

theorem nb089_fresh_065 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_020 u A B R) ∉ (((Wff.classMem (Class.cv (nb089_alpha_dummy_017 u A B R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb089_alpha_dummy_017 u A B R)) (syn_c1c))).fv ∪ ((Class.cv (nb089_alpha_dummy_017 u A B R))).fv) := by
  simpa only [nb089_alpha_dummy_020] using freshVar_not_mem (((Wff.classMem (Class.cv (nb089_alpha_dummy_017 u A B R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb089_alpha_dummy_017 u A B R)) (syn_c1c))).fv ∪ ((Class.cv (nb089_alpha_dummy_017 u A B R))).fv) 0

theorem nb089_fresh_066 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_059 A B R) ∉ (((Wff.classMem (Class.cv (nb089_alpha_dummy_055 A B R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb089_alpha_dummy_055 A B R)) (syn_c1c))).fv ∪ ((Class.cv (nb089_alpha_dummy_055 A B R))).fv) := by
  simpa only [nb089_alpha_dummy_059] using freshVar_not_mem (((Wff.classMem (Class.cv (nb089_alpha_dummy_055 A B R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb089_alpha_dummy_055 A B R)) (syn_c1c))).fv ∪ ((Class.cv (nb089_alpha_dummy_055 A B R))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
