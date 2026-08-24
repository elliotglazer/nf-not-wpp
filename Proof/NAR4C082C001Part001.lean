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

noncomputable def nb082_alpha_dummy_000 (A : Class) (B : Class) (R : Class) : Var := (freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0)

noncomputable def nb082_alpha_dummy_001 (A : Class) (B : Class) (R : Class) : Var := (freshVar (({(nb082_alpha_dummy_000 A B R)} : Finset Var) ∪ ((syn_cxpk B B)).fv ∪ ((syn_cfdminvalp R A B (Class.cv (nb082_alpha_dummy_000 A B R)))).fv) 0)

noncomputable def nb082_alpha_dummy_002 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (({p} : Finset Var) ∪ ((syn_cxpk B B)).fv ∪ ((syn_cfdminvalp R A B (Class.cv p))).fv) 0)

noncomputable def nb082_alpha_dummy_003 (A : Class) (B : Class) (R : Class) : Var := (freshVar (({(nb082_alpha_dummy_000 A B R)} : Finset Var) ∪ ({(nb082_alpha_dummy_001 A B R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb082_alpha_dummy_000 A B R)) (syn_cxpk B B)) (Wff.classEq (Class.cv (nb082_alpha_dummy_001 A B R)) (syn_cfdminvalp R A B (Class.cv (nb082_alpha_dummy_000 A B R)))))).fv) 0)

noncomputable def nb082_alpha_dummy_004 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (({p} : Finset Var) ∪ ({(nb082_alpha_dummy_002 A B R p)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv p) (syn_cxpk B B)) (Wff.classEq (Class.cv (nb082_alpha_dummy_002 A B R p)) (syn_cfdminvalp R A B (Class.cv p))))).fv) 0)

noncomputable def nb082_alpha_dummy_005 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb082_alpha_dummy_000 A B R))).fv ∪ ((Class.cv (nb082_alpha_dummy_001 A B R))).fv) 0)

noncomputable def nb082_alpha_dummy_006 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb082_alpha_dummy_000 A B R))).fv ∪ ((Class.cv (nb082_alpha_dummy_001 A B R))).fv) 1)

noncomputable def nb082_alpha_dummy_007 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((Class.cv p)).fv ∪ ((Class.cv (nb082_alpha_dummy_002 A B R p))).fv) 0)

noncomputable def nb082_alpha_dummy_008 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((Class.cv p)).fv ∪ ((Class.cv (nb082_alpha_dummy_002 A B R p))).fv) 1)

noncomputable def nb082_alpha_dummy_009 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_001 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb082_alpha_dummy_010 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv p) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p)))))))).fv ∪ ((syn_ccompl (Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv (nb082_alpha_dummy_002 A B R p)) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb082_alpha_dummy_011 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))))))).fv ∪ ((Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))))))).fv) 0)

noncomputable def nb082_alpha_dummy_012 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv p) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))))))).fv ∪ ((Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv p) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))))))).fv) 0)

noncomputable def nb082_alpha_dummy_013 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb082_alpha_dummy_006 A B R))).fv) 0)

noncomputable def nb082_alpha_dummy_014 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb082_alpha_dummy_006 A B R))).fv) 1)

noncomputable def nb082_alpha_dummy_015 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((Class.cv (nb082_alpha_dummy_008 A B R p))).fv) 0)

noncomputable def nb082_alpha_dummy_016 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((Class.cv (nb082_alpha_dummy_008 A B R p))).fv) 1)

noncomputable def nb082_alpha_dummy_017 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb082_alpha_dummy_013 A B R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb082_alpha_dummy_013 A B R)) (syn_c1c))).fv ∪ ((Class.cv (nb082_alpha_dummy_013 A B R))).fv) 0)

noncomputable def nb082_alpha_dummy_018 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb082_alpha_dummy_015 A B R p)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb082_alpha_dummy_015 A B R p)) (syn_c1c))).fv ∪ ((Class.cv (nb082_alpha_dummy_015 A B R p))).fv) 0)

noncomputable def nb082_alpha_dummy_019 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb082_alpha_dummy_013 A B R))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb082_alpha_dummy_020 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb082_alpha_dummy_013 A B R))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb082_alpha_dummy_021 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb082_alpha_dummy_013 A B R))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb082_alpha_dummy_022 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb082_alpha_dummy_023 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb082_alpha_dummy_024 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb082_alpha_dummy_025 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb082_alpha_dummy_020 A B R)) (Class.cv (nb082_alpha_dummy_021 A B R)))).fv ∪ ((syn_cnin (Class.cv (nb082_alpha_dummy_020 A B R)) (Class.cv (nb082_alpha_dummy_021 A B R)))).fv) 0)

noncomputable def nb082_alpha_dummy_026 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb082_alpha_dummy_023 A B R p)) (Class.cv (nb082_alpha_dummy_024 A B R p)))).fv ∪ ((syn_cnin (Class.cv (nb082_alpha_dummy_023 A B R p)) (Class.cv (nb082_alpha_dummy_024 A B R p)))).fv) 0)

noncomputable def nb082_alpha_dummy_027 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb082_alpha_dummy_020 A B R))).fv ∪ ((Class.cv (nb082_alpha_dummy_021 A B R))).fv) 0)

noncomputable def nb082_alpha_dummy_028 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((Class.cv (nb082_alpha_dummy_023 A B R p))).fv ∪ ((Class.cv (nb082_alpha_dummy_024 A B R p))).fv) 0)

noncomputable def nb082_alpha_dummy_029 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb082_alpha_dummy_020 A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb082_alpha_dummy_021 A B R)))).fv) 0)

noncomputable def nb082_alpha_dummy_030 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb082_alpha_dummy_023 A B R p)))).fv ∪ ((syn_ccompl (Class.cv (nb082_alpha_dummy_024 A B R p)))).fv) 0)

noncomputable def nb082_alpha_dummy_031 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb082_alpha_dummy_020 A B R))).fv ∪ ((Class.cv (nb082_alpha_dummy_020 A B R))).fv) 0)

noncomputable def nb082_alpha_dummy_032 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((Class.cv (nb082_alpha_dummy_023 A B R p))).fv ∪ ((Class.cv (nb082_alpha_dummy_023 A B R p))).fv) 0)

noncomputable def nb082_alpha_dummy_033 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb082_alpha_dummy_021 A B R))).fv ∪ ((Class.cv (nb082_alpha_dummy_021 A B R))).fv) 0)

noncomputable def nb082_alpha_dummy_034 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((Class.cv (nb082_alpha_dummy_024 A B R p))).fv ∪ ((Class.cv (nb082_alpha_dummy_024 A B R p))).fv) 0)

noncomputable def nb082_alpha_dummy_035 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_001 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_001 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb082_alpha_dummy_036 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv (nb082_alpha_dummy_002 A B R p)) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv (nb082_alpha_dummy_002 A B R p)) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb082_alpha_dummy_037 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb082_alpha_dummy_038 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb082_alpha_dummy_039 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R)))).fv ∪ ((syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R)))).fv) 0)

noncomputable def nb082_alpha_dummy_040 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p)))).fv ∪ ((syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p)))).fv) 0)

noncomputable def nb082_alpha_dummy_041 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv) 0)

noncomputable def nb082_alpha_dummy_042 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv) 1)

noncomputable def nb082_alpha_dummy_043 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))) (syn_c1c))).fv) 0)

noncomputable def nb082_alpha_dummy_044 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))) (syn_c1c))).fv) 1)

noncomputable def nb082_alpha_dummy_045 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv ∪ ((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv) 0)

noncomputable def nb082_alpha_dummy_046 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))) (syn_c1c))).fv ∪ ((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))) (syn_c1c))).fv) 0)

noncomputable def nb082_alpha_dummy_047 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R))))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb082_alpha_dummy_048 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb082_alpha_dummy_049 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))).fv) 0)

noncomputable def nb082_alpha_dummy_050 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))).fv) 1)

noncomputable def nb082_alpha_dummy_051 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn (Class.cv p))).fv) 0)

noncomputable def nb082_alpha_dummy_052 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn (Class.cv p))).fv) 1)

noncomputable def nb082_alpha_dummy_053 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb082_alpha_dummy_000 A B R))).fv) 0)

noncomputable def nb082_alpha_dummy_054 (p : Var) : Var := (freshVar (((Class.cv p)).fv) 0)

noncomputable def nb082_alpha_dummy_055 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_ccompl (syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_050 A B R)))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_050 A B R)) (Class.cv (nb082_alpha_dummy_049 A B R)))))).fv) 0)

noncomputable def nb082_alpha_dummy_056 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((syn_ccompl (syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p)))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_052 A B R p)) (Class.cv (nb082_alpha_dummy_051 A B R p)))))).fv) 0)

noncomputable def nb082_alpha_dummy_057 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_050 A B R))))).fv ∪ ((syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_050 A B R))))).fv) 0)

noncomputable def nb082_alpha_dummy_058 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p))))).fv ∪ ((syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p))))).fv) 0)

noncomputable def nb082_alpha_dummy_059 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_csn (Class.cv (nb082_alpha_dummy_050 A B R)))).fv) 0)

noncomputable def nb082_alpha_dummy_060 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p)))).fv) 0)

noncomputable def nb082_alpha_dummy_061 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb082_alpha_dummy_050 A B R))).fv) 0)

noncomputable def nb082_alpha_dummy_062 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((Class.cv (nb082_alpha_dummy_052 A B R p))).fv) 0)

noncomputable def nb082_alpha_dummy_063 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_050 A B R)) (Class.cv (nb082_alpha_dummy_049 A B R))))).fv ∪ ((syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_050 A B R)) (Class.cv (nb082_alpha_dummy_049 A B R))))).fv) 0)

noncomputable def nb082_alpha_dummy_064 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_052 A B R p)) (Class.cv (nb082_alpha_dummy_051 A B R p))))).fv ∪ ((syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_052 A B R p)) (Class.cv (nb082_alpha_dummy_051 A B R p))))).fv) 0)

noncomputable def nb082_alpha_dummy_065 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_cpr (Class.cv (nb082_alpha_dummy_050 A B R)) (Class.cv (nb082_alpha_dummy_049 A B R)))).fv) 0)

noncomputable def nb082_alpha_dummy_066 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((syn_cpr (Class.cv (nb082_alpha_dummy_052 A B R p)) (Class.cv (nb082_alpha_dummy_051 A B R p)))).fv) 0)

noncomputable def nb082_alpha_dummy_067 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_ccompl (syn_csn (Class.cv (nb082_alpha_dummy_050 A B R))))).fv ∪ ((syn_ccompl (syn_csn (Class.cv (nb082_alpha_dummy_049 A B R))))).fv) 0)

noncomputable def nb082_alpha_dummy_068 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((syn_ccompl (syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p))))).fv ∪ ((syn_ccompl (syn_csn (Class.cv (nb082_alpha_dummy_051 A B R p))))).fv) 0)

noncomputable def nb082_alpha_dummy_069 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_csn (Class.cv (nb082_alpha_dummy_050 A B R)))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_050 A B R)))).fv) 0)

noncomputable def nb082_alpha_dummy_070 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p)))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p)))).fv) 0)

noncomputable def nb082_alpha_dummy_071 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((syn_csn (Class.cv (nb082_alpha_dummy_049 A B R)))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_049 A B R)))).fv) 0)

noncomputable def nb082_alpha_dummy_072 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((syn_csn (Class.cv (nb082_alpha_dummy_051 A B R p)))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_051 A B R p)))).fv) 0)

noncomputable def nb082_alpha_dummy_073 (A : Class) (B : Class) (R : Class) : Var := (freshVar (((Class.cv (nb082_alpha_dummy_049 A B R))).fv) 0)

noncomputable def nb082_alpha_dummy_074 (A : Class) (B : Class) (R : Class) (p : Var) : Var := (freshVar (((Class.cv (nb082_alpha_dummy_051 A B R p))).fv) 0)

theorem nb082_fresh_000 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_011 A B R) ∉ (((Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))))))).fv ∪ ((Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))))))).fv) := by
  simpa only [nb082_alpha_dummy_011] using freshVar_not_mem (((Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))))))).fv ∪ ((Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))))))).fv) 0

theorem nb082_fresh_001 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_035 A B R) ∉ (((Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_001 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_001 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb082_alpha_dummy_035] using freshVar_not_mem (((Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_001 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_001 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb082_fresh_002 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_036 A B R p) ∉ (((Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv (nb082_alpha_dummy_002 A B R p)) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv (nb082_alpha_dummy_002 A B R p)) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb082_alpha_dummy_036] using freshVar_not_mem (((Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv (nb082_alpha_dummy_002 A B R p)) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv (nb082_alpha_dummy_002 A B R p)) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb082_fresh_003 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_012 A B R p) ∉ (((Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv p) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))))))).fv ∪ ((Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv p) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))))))).fv) := by
  simpa only [nb082_alpha_dummy_012] using freshVar_not_mem (((Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv p) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))))))).fv ∪ ((Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv p) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))))))).fv) 0

theorem nb082_fresh_004 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_053 A B R) ∉ (((Class.cv (nb082_alpha_dummy_000 A B R))).fv) := by
  simpa only [nb082_alpha_dummy_053] using freshVar_not_mem (((Class.cv (nb082_alpha_dummy_000 A B R))).fv) 0

theorem nb082_fresh_005 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_005 A B R) ∉ (((Class.cv (nb082_alpha_dummy_000 A B R))).fv ∪ ((Class.cv (nb082_alpha_dummy_001 A B R))).fv) := by
  simpa only [nb082_alpha_dummy_005] using freshVar_not_mem (((Class.cv (nb082_alpha_dummy_000 A B R))).fv ∪ ((Class.cv (nb082_alpha_dummy_001 A B R))).fv) 0

theorem nb082_fresh_006 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_006 A B R) ∉ (((Class.cv (nb082_alpha_dummy_000 A B R))).fv ∪ ((Class.cv (nb082_alpha_dummy_001 A B R))).fv) := by
  simpa only [nb082_alpha_dummy_006] using freshVar_not_mem (((Class.cv (nb082_alpha_dummy_000 A B R))).fv ∪ ((Class.cv (nb082_alpha_dummy_001 A B R))).fv) 1

theorem nb082_distinct_007 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_005 A B R) ≠ (nb082_alpha_dummy_006 A B R) := by
  simpa only [nb082_alpha_dummy_005, nb082_alpha_dummy_006] using
    (freshVar_injective (((Class.cv (nb082_alpha_dummy_000 A B R))).fv ∪ ((Class.cv (nb082_alpha_dummy_001 A B R))).fv) (i := 0) (j := 1) (by decide))

theorem nb082_fresh_008 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_013 A B R) ∉ (((Class.cv (nb082_alpha_dummy_006 A B R))).fv) := by
  simpa only [nb082_alpha_dummy_013] using freshVar_not_mem (((Class.cv (nb082_alpha_dummy_006 A B R))).fv) 0

theorem nb082_fresh_009 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_014 A B R) ∉ (((Class.cv (nb082_alpha_dummy_006 A B R))).fv) := by
  simpa only [nb082_alpha_dummy_014] using freshVar_not_mem (((Class.cv (nb082_alpha_dummy_006 A B R))).fv) 1

theorem nb082_distinct_010 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_013 A B R) ≠ (nb082_alpha_dummy_014 A B R) := by
  simpa only [nb082_alpha_dummy_013, nb082_alpha_dummy_014] using
    (freshVar_injective (((Class.cv (nb082_alpha_dummy_006 A B R))).fv) (i := 0) (j := 1) (by decide))

theorem nb082_fresh_011 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_015 A B R p) ∉ (((Class.cv (nb082_alpha_dummy_008 A B R p))).fv) := by
  simpa only [nb082_alpha_dummy_015] using freshVar_not_mem (((Class.cv (nb082_alpha_dummy_008 A B R p))).fv) 0

theorem nb082_fresh_012 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_016 A B R p) ∉ (((Class.cv (nb082_alpha_dummy_008 A B R p))).fv) := by
  simpa only [nb082_alpha_dummy_016] using freshVar_not_mem (((Class.cv (nb082_alpha_dummy_008 A B R p))).fv) 1

theorem nb082_distinct_013 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_016 A B R p) := by
  simpa only [nb082_alpha_dummy_015, nb082_alpha_dummy_016] using
    (freshVar_injective (((Class.cv (nb082_alpha_dummy_008 A B R p))).fv) (i := 0) (j := 1) (by decide))

theorem nb082_fresh_014 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_019 A B R) ∉ (((Class.cv (nb082_alpha_dummy_013 A B R))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb082_alpha_dummy_019] using freshVar_not_mem (((Class.cv (nb082_alpha_dummy_013 A B R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb082_fresh_015 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_020 A B R) ∉ (((Class.cv (nb082_alpha_dummy_013 A B R))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb082_alpha_dummy_020] using freshVar_not_mem (((Class.cv (nb082_alpha_dummy_013 A B R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb082_fresh_016 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_021 A B R) ∉ (((Class.cv (nb082_alpha_dummy_013 A B R))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb082_alpha_dummy_021] using freshVar_not_mem (((Class.cv (nb082_alpha_dummy_013 A B R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb082_distinct_017 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_019 A B R) ≠ (nb082_alpha_dummy_020 A B R) := by
  simpa only [nb082_alpha_dummy_019, nb082_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb082_alpha_dummy_013 A B R))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb082_distinct_018 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_019 A B R) ≠ (nb082_alpha_dummy_021 A B R) := by
  simpa only [nb082_alpha_dummy_019, nb082_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb082_alpha_dummy_013 A B R))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb082_distinct_019 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_020 A B R) ≠ (nb082_alpha_dummy_021 A B R) := by
  simpa only [nb082_alpha_dummy_020, nb082_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb082_alpha_dummy_013 A B R))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb082_fresh_020 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_022 A B R p) ∉ (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb082_alpha_dummy_022] using freshVar_not_mem (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪ ((syn_c1c)).fv) 0

theorem nb082_fresh_021 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_023 A B R p) ∉ (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb082_alpha_dummy_023] using freshVar_not_mem (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪ ((syn_c1c)).fv) 1

theorem nb082_fresh_022 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_024 A B R p) ∉ (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb082_alpha_dummy_024] using freshVar_not_mem (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪ ((syn_c1c)).fv) 2

theorem nb082_distinct_023 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_022 A B R p) ≠ (nb082_alpha_dummy_023 A B R p) := by
  simpa only [nb082_alpha_dummy_022, nb082_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb082_distinct_024 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_022 A B R p) ≠ (nb082_alpha_dummy_024 A B R p) := by
  simpa only [nb082_alpha_dummy_022, nb082_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb082_distinct_025 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_024 A B R p) := by
  simpa only [nb082_alpha_dummy_023, nb082_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb082_fresh_026 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_031 A B R) ∉ (((Class.cv (nb082_alpha_dummy_020 A B R))).fv ∪ ((Class.cv (nb082_alpha_dummy_020 A B R))).fv) := by
  simpa only [nb082_alpha_dummy_031] using freshVar_not_mem (((Class.cv (nb082_alpha_dummy_020 A B R))).fv ∪ ((Class.cv (nb082_alpha_dummy_020 A B R))).fv) 0

theorem nb082_fresh_027 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_027 A B R) ∉ (((Class.cv (nb082_alpha_dummy_020 A B R))).fv ∪ ((Class.cv (nb082_alpha_dummy_021 A B R))).fv) := by
  simpa only [nb082_alpha_dummy_027] using freshVar_not_mem (((Class.cv (nb082_alpha_dummy_020 A B R))).fv ∪ ((Class.cv (nb082_alpha_dummy_021 A B R))).fv) 0

theorem nb082_fresh_028 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_033 A B R) ∉ (((Class.cv (nb082_alpha_dummy_021 A B R))).fv ∪ ((Class.cv (nb082_alpha_dummy_021 A B R))).fv) := by
  simpa only [nb082_alpha_dummy_033] using freshVar_not_mem (((Class.cv (nb082_alpha_dummy_021 A B R))).fv ∪ ((Class.cv (nb082_alpha_dummy_021 A B R))).fv) 0

theorem nb082_fresh_029 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_032 A B R p) ∉ (((Class.cv (nb082_alpha_dummy_023 A B R p))).fv ∪ ((Class.cv (nb082_alpha_dummy_023 A B R p))).fv) := by
  simpa only [nb082_alpha_dummy_032] using freshVar_not_mem (((Class.cv (nb082_alpha_dummy_023 A B R p))).fv ∪ ((Class.cv (nb082_alpha_dummy_023 A B R p))).fv) 0

theorem nb082_fresh_030 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_028 A B R p) ∉ (((Class.cv (nb082_alpha_dummy_023 A B R p))).fv ∪ ((Class.cv (nb082_alpha_dummy_024 A B R p))).fv) := by
  simpa only [nb082_alpha_dummy_028] using freshVar_not_mem (((Class.cv (nb082_alpha_dummy_023 A B R p))).fv ∪ ((Class.cv (nb082_alpha_dummy_024 A B R p))).fv) 0

theorem nb082_fresh_031 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_034 A B R p) ∉ (((Class.cv (nb082_alpha_dummy_024 A B R p))).fv ∪ ((Class.cv (nb082_alpha_dummy_024 A B R p))).fv) := by
  simpa only [nb082_alpha_dummy_034] using freshVar_not_mem (((Class.cv (nb082_alpha_dummy_024 A B R p))).fv ∪ ((Class.cv (nb082_alpha_dummy_024 A B R p))).fv) 0

theorem nb082_fresh_032 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_073 A B R) ∉ (((Class.cv (nb082_alpha_dummy_049 A B R))).fv) := by
  simpa only [nb082_alpha_dummy_073] using freshVar_not_mem (((Class.cv (nb082_alpha_dummy_049 A B R))).fv) 0

theorem nb082_fresh_033 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_061 A B R) ∉ (((Class.cv (nb082_alpha_dummy_050 A B R))).fv) := by
  simpa only [nb082_alpha_dummy_061] using freshVar_not_mem (((Class.cv (nb082_alpha_dummy_050 A B R))).fv) 0

theorem nb082_fresh_034 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_074 A B R p) ∉ (((Class.cv (nb082_alpha_dummy_051 A B R p))).fv) := by
  simpa only [nb082_alpha_dummy_074] using freshVar_not_mem (((Class.cv (nb082_alpha_dummy_051 A B R p))).fv) 0

theorem nb082_fresh_035 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_062 A B R p) ∉ (((Class.cv (nb082_alpha_dummy_052 A B R p))).fv) := by
  simpa only [nb082_alpha_dummy_062] using freshVar_not_mem (((Class.cv (nb082_alpha_dummy_052 A B R p))).fv) 0

theorem nb082_fresh_036 (p : Var) : (nb082_alpha_dummy_054 p) ∉ (((Class.cv p)).fv) := by
  simpa only [nb082_alpha_dummy_054] using freshVar_not_mem (((Class.cv p)).fv) 0

theorem nb082_fresh_037 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_007 A B R p) ∉ (((Class.cv p)).fv ∪ ((Class.cv (nb082_alpha_dummy_002 A B R p))).fv) := by
  simpa only [nb082_alpha_dummy_007] using freshVar_not_mem (((Class.cv p)).fv ∪ ((Class.cv (nb082_alpha_dummy_002 A B R p))).fv) 0

theorem nb082_fresh_038 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_008 A B R p) ∉ (((Class.cv p)).fv ∪ ((Class.cv (nb082_alpha_dummy_002 A B R p))).fv) := by
  simpa only [nb082_alpha_dummy_008] using freshVar_not_mem (((Class.cv p)).fv ∪ ((Class.cv (nb082_alpha_dummy_002 A B R p))).fv) 1

theorem nb082_distinct_039 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_007 A B R p) ≠ (nb082_alpha_dummy_008 A B R p) := by
  simpa only [nb082_alpha_dummy_007, nb082_alpha_dummy_008] using
    (freshVar_injective (((Class.cv p)).fv ∪ ((Class.cv (nb082_alpha_dummy_002 A B R p))).fv) (i := 0) (j := 1) (by decide))

theorem nb082_fresh_040 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_017 A B R) ∉ (((Wff.classMem (Class.cv (nb082_alpha_dummy_013 A B R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb082_alpha_dummy_013 A B R)) (syn_c1c))).fv ∪ ((Class.cv (nb082_alpha_dummy_013 A B R))).fv) := by
  simpa only [nb082_alpha_dummy_017] using freshVar_not_mem (((Wff.classMem (Class.cv (nb082_alpha_dummy_013 A B R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb082_alpha_dummy_013 A B R)) (syn_c1c))).fv ∪ ((Class.cv (nb082_alpha_dummy_013 A B R))).fv) 0

theorem nb082_fresh_041 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_018 A B R p) ∉ (((Wff.classMem (Class.cv (nb082_alpha_dummy_015 A B R p)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb082_alpha_dummy_015 A B R p)) (syn_c1c))).fv ∪ ((Class.cv (nb082_alpha_dummy_015 A B R p))).fv) := by
  simpa only [nb082_alpha_dummy_018] using freshVar_not_mem (((Wff.classMem (Class.cv (nb082_alpha_dummy_015 A B R p)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb082_alpha_dummy_015 A B R p)) (syn_c1c))).fv ∪ ((Class.cv (nb082_alpha_dummy_015 A B R p))).fv) 0

theorem nb082_fresh_042 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_049 A B R) ∉ (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))).fv) := by
  simpa only [nb082_alpha_dummy_049] using freshVar_not_mem (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))).fv) 0

theorem nb082_fresh_043 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_050 A B R) ∉ (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))).fv) := by
  simpa only [nb082_alpha_dummy_050] using freshVar_not_mem (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))).fv) 1

theorem nb082_distinct_044 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_049 A B R) ≠ (nb082_alpha_dummy_050 A B R) := by
  simpa only [nb082_alpha_dummy_049, nb082_alpha_dummy_050] using
    (freshVar_injective (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))).fv) (i := 0) (j := 1) (by decide))

theorem nb082_fresh_045 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_051 A B R p) ∉ (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn (Class.cv p))).fv) := by
  simpa only [nb082_alpha_dummy_051] using freshVar_not_mem (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn (Class.cv p))).fv) 0

theorem nb082_fresh_046 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_052 A B R p) ∉ (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn (Class.cv p))).fv) := by
  simpa only [nb082_alpha_dummy_052] using freshVar_not_mem (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn (Class.cv p))).fv) 1

theorem nb082_distinct_047 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_052 A B R p) := by
  simpa only [nb082_alpha_dummy_051, nb082_alpha_dummy_052] using
    (freshVar_injective (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn (Class.cv p))).fv) (i := 0) (j := 1) (by decide))

theorem nb082_fresh_048 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_009 A B R) ∉ (((syn_ccompl (Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_001 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb082_alpha_dummy_009] using freshVar_not_mem (((syn_ccompl (Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_001 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb082_fresh_049 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_010 A B R p) ∉ (((syn_ccompl (Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv p) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p)))))))).fv ∪ ((syn_ccompl (Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv (nb082_alpha_dummy_002 A B R p)) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb082_alpha_dummy_010] using freshVar_not_mem (((syn_ccompl (Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv p) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p)))))))).fv ∪ ((syn_ccompl (Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv (nb082_alpha_dummy_002 A B R p)) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb082_fresh_050 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_029 A B R) ∉ (((syn_ccompl (Class.cv (nb082_alpha_dummy_020 A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb082_alpha_dummy_021 A B R)))).fv) := by
  simpa only [nb082_alpha_dummy_029] using freshVar_not_mem (((syn_ccompl (Class.cv (nb082_alpha_dummy_020 A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb082_alpha_dummy_021 A B R)))).fv) 0

theorem nb082_fresh_051 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_030 A B R p) ∉ (((syn_ccompl (Class.cv (nb082_alpha_dummy_023 A B R p)))).fv ∪ ((syn_ccompl (Class.cv (nb082_alpha_dummy_024 A B R p)))).fv) := by
  simpa only [nb082_alpha_dummy_030] using freshVar_not_mem (((syn_ccompl (Class.cv (nb082_alpha_dummy_023 A B R p)))).fv ∪ ((syn_ccompl (Class.cv (nb082_alpha_dummy_024 A B R p)))).fv) 0

theorem nb082_fresh_052 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_037 A B R) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb082_alpha_dummy_037] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb082_fresh_053 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_038 A B R p) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb082_alpha_dummy_038] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb082_fresh_054 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_067 A B R) ∉ (((syn_ccompl (syn_csn (Class.cv (nb082_alpha_dummy_050 A B R))))).fv ∪ ((syn_ccompl (syn_csn (Class.cv (nb082_alpha_dummy_049 A B R))))).fv) := by
  simpa only [nb082_alpha_dummy_067] using freshVar_not_mem (((syn_ccompl (syn_csn (Class.cv (nb082_alpha_dummy_050 A B R))))).fv ∪ ((syn_ccompl (syn_csn (Class.cv (nb082_alpha_dummy_049 A B R))))).fv) 0

theorem nb082_fresh_055 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_068 A B R p) ∉ (((syn_ccompl (syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p))))).fv ∪ ((syn_ccompl (syn_csn (Class.cv (nb082_alpha_dummy_051 A B R p))))).fv) := by
  simpa only [nb082_alpha_dummy_068] using freshVar_not_mem (((syn_ccompl (syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p))))).fv ∪ ((syn_ccompl (syn_csn (Class.cv (nb082_alpha_dummy_051 A B R p))))).fv) 0

theorem nb082_fresh_056 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_055 A B R) ∉ (((syn_ccompl (syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_050 A B R)))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_050 A B R)) (Class.cv (nb082_alpha_dummy_049 A B R)))))).fv) := by
  simpa only [nb082_alpha_dummy_055] using freshVar_not_mem (((syn_ccompl (syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_050 A B R)))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_050 A B R)) (Class.cv (nb082_alpha_dummy_049 A B R)))))).fv) 0

theorem nb082_fresh_057 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_056 A B R p) ∉ (((syn_ccompl (syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p)))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_052 A B R p)) (Class.cv (nb082_alpha_dummy_051 A B R p)))))).fv) := by
  simpa only [nb082_alpha_dummy_056] using freshVar_not_mem (((syn_ccompl (syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p)))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_052 A B R p)) (Class.cv (nb082_alpha_dummy_051 A B R p)))))).fv) 0

theorem nb082_fresh_058 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_047 A B R) ∉ (((syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R))))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb082_alpha_dummy_047] using freshVar_not_mem (((syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R))))).fv ∪ ((syn_c1c)).fv) 0

theorem nb082_fresh_059 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_048 A B R p) ∉ (((syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb082_alpha_dummy_048] using freshVar_not_mem (((syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))).fv ∪ ((syn_c1c)).fv) 0

theorem nb082_fresh_060 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_041 A B R) ∉ (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv) := by
  simpa only [nb082_alpha_dummy_041] using freshVar_not_mem (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv) 0

theorem nb082_fresh_061 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_042 A B R) ∉ (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv) := by
  simpa only [nb082_alpha_dummy_042] using freshVar_not_mem (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv) 1

theorem nb082_distinct_062 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_041 A B R) ≠ (nb082_alpha_dummy_042 A B R) := by
  simpa only [nb082_alpha_dummy_041, nb082_alpha_dummy_042] using
    (freshVar_injective (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv) (i := 0) (j := 1) (by decide))

theorem nb082_fresh_063 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_043 A B R p) ∉ (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))) (syn_c1c))).fv) := by
  simpa only [nb082_alpha_dummy_043] using freshVar_not_mem (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))) (syn_c1c))).fv) 0

theorem nb082_fresh_064 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_044 A B R p) ∉ (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))) (syn_c1c))).fv) := by
  simpa only [nb082_alpha_dummy_044] using freshVar_not_mem (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))) (syn_c1c))).fv) 1

theorem nb082_distinct_065 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_043 A B R p) ≠ (nb082_alpha_dummy_044 A B R p) := by
  simpa only [nb082_alpha_dummy_043, nb082_alpha_dummy_044] using
    (freshVar_injective (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))) (syn_c1c))).fv) (i := 0) (j := 1) (by decide))

theorem nb082_fresh_066 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_025 A B R) ∉ (((syn_cnin (Class.cv (nb082_alpha_dummy_020 A B R)) (Class.cv (nb082_alpha_dummy_021 A B R)))).fv ∪ ((syn_cnin (Class.cv (nb082_alpha_dummy_020 A B R)) (Class.cv (nb082_alpha_dummy_021 A B R)))).fv) := by
  simpa only [nb082_alpha_dummy_025] using freshVar_not_mem (((syn_cnin (Class.cv (nb082_alpha_dummy_020 A B R)) (Class.cv (nb082_alpha_dummy_021 A B R)))).fv ∪ ((syn_cnin (Class.cv (nb082_alpha_dummy_020 A B R)) (Class.cv (nb082_alpha_dummy_021 A B R)))).fv) 0

theorem nb082_fresh_067 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_026 A B R p) ∉ (((syn_cnin (Class.cv (nb082_alpha_dummy_023 A B R p)) (Class.cv (nb082_alpha_dummy_024 A B R p)))).fv ∪ ((syn_cnin (Class.cv (nb082_alpha_dummy_023 A B R p)) (Class.cv (nb082_alpha_dummy_024 A B R p)))).fv) := by
  simpa only [nb082_alpha_dummy_026] using freshVar_not_mem (((syn_cnin (Class.cv (nb082_alpha_dummy_023 A B R p)) (Class.cv (nb082_alpha_dummy_024 A B R p)))).fv ∪ ((syn_cnin (Class.cv (nb082_alpha_dummy_023 A B R p)) (Class.cv (nb082_alpha_dummy_024 A B R p)))).fv) 0

theorem nb082_fresh_068 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_045 A B R) ∉ (((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv ∪ ((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv) := by
  simpa only [nb082_alpha_dummy_045] using freshVar_not_mem (((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv ∪ ((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv) 0

theorem nb082_fresh_069 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_046 A B R p) ∉ (((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))) (syn_c1c))).fv ∪ ((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))) (syn_c1c))).fv) := by
  simpa only [nb082_alpha_dummy_046] using freshVar_not_mem (((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))) (syn_c1c))).fv ∪ ((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))) (syn_c1c))).fv) 0

theorem nb082_fresh_070 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_039 A B R) ∉ (((syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R)))).fv ∪ ((syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R)))).fv) := by
  simpa only [nb082_alpha_dummy_039] using freshVar_not_mem (((syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R)))).fv ∪ ((syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R)))).fv) 0

theorem nb082_fresh_071 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_040 A B R p) ∉ (((syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p)))).fv ∪ ((syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p)))).fv) := by
  simpa only [nb082_alpha_dummy_040] using freshVar_not_mem (((syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p)))).fv ∪ ((syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p)))).fv) 0

theorem nb082_fresh_072 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_065 A B R) ∉ (((syn_cpr (Class.cv (nb082_alpha_dummy_050 A B R)) (Class.cv (nb082_alpha_dummy_049 A B R)))).fv) := by
  simpa only [nb082_alpha_dummy_065] using freshVar_not_mem (((syn_cpr (Class.cv (nb082_alpha_dummy_050 A B R)) (Class.cv (nb082_alpha_dummy_049 A B R)))).fv) 0

theorem nb082_fresh_073 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_066 A B R p) ∉ (((syn_cpr (Class.cv (nb082_alpha_dummy_052 A B R p)) (Class.cv (nb082_alpha_dummy_051 A B R p)))).fv) := by
  simpa only [nb082_alpha_dummy_066] using freshVar_not_mem (((syn_cpr (Class.cv (nb082_alpha_dummy_052 A B R p)) (Class.cv (nb082_alpha_dummy_051 A B R p)))).fv) 0

theorem nb082_fresh_074 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_071 A B R) ∉ (((syn_csn (Class.cv (nb082_alpha_dummy_049 A B R)))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_049 A B R)))).fv) := by
  simpa only [nb082_alpha_dummy_071] using freshVar_not_mem (((syn_csn (Class.cv (nb082_alpha_dummy_049 A B R)))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_049 A B R)))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
