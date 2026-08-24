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

noncomputable def nb090_alpha_dummy_000 (A : Class) : Var := (freshVar ((A).fv) 0)

noncomputable def nb090_alpha_dummy_001 (A : Class) : Var := (freshVar ((A).fv) 1)

noncomputable def nb090_alpha_dummy_002 (A : Class) : Var := (freshVar ((A).fv) 2)

noncomputable def nb090_alpha_dummy_003 (A : Class) : Var := (freshVar (({(nb090_alpha_dummy_001 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_002 A)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb090_alpha_dummy_001 A)) (syn_chwcodes A)) (Wff.classMem (Class.cv (nb090_alpha_dummy_002 A)) (syn_chwcodes A))) (syn_wex (nb090_alpha_dummy_000 A) (syn_wiso (Class.cv (nb090_alpha_dummy_000 A)) (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A))) (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A))) (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A))) (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))))).fv) 0)

noncomputable def nb090_alpha_dummy_004 (v : Var) (u : Var) (A : Class) (h : Var) : Var := (freshVar (({u} : Finset Var) ∪ ({v} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv u) (syn_chwcodes A)) (Wff.classMem (Class.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (Class.cv h) (syn_cfv (syn_c1st) (Class.cv u)) (syn_cfv (syn_c1st) (Class.cv v)) (syn_cfv (syn_c2nd) (Class.cv u)) (syn_cfv (syn_c2nd) (Class.cv v)))))).fv) 0)

noncomputable def nb090_alpha_dummy_005 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) 0)

noncomputable def nb090_alpha_dummy_006 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) 1)

noncomputable def nb090_alpha_dummy_007 (v : Var) (u : Var) : Var := (freshVar (((Class.cv u)).fv ∪ ((Class.cv v)).fv) 0)

noncomputable def nb090_alpha_dummy_008 (v : Var) (u : Var) : Var := (freshVar (((Class.cv u)).fv ∪ ((Class.cv v)).fv) 1)

noncomputable def nb090_alpha_dummy_009 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_005 A) (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_005 A) (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_010 (v : Var) (u : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_007 v u) (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u)) (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_007 v u) (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_011 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_005 A) (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_005 A) (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))))))).fv) 0)

noncomputable def nb090_alpha_dummy_012 (v : Var) (u : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_007 v u) (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u)) (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_007 v u) (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u)) (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))))))).fv) 0)

noncomputable def nb090_alpha_dummy_013 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_006 A))).fv) 0)

noncomputable def nb090_alpha_dummy_014 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_006 A))).fv) 1)

noncomputable def nb090_alpha_dummy_015 (v : Var) (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_008 v u))).fv) 0)

noncomputable def nb090_alpha_dummy_016 (v : Var) (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_008 v u))).fv) 1)

noncomputable def nb090_alpha_dummy_017 (A : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_013 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_013 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_013 A))).fv) 0)

noncomputable def nb090_alpha_dummy_018 (v : Var) (u : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_015 v u)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_015 v u)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_015 v u))).fv) 0)

noncomputable def nb090_alpha_dummy_019 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_020 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_021 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_022 (v : Var) (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_023 (v : Var) (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_024 (v : Var) (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_025 (A : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_020 A)) (Class.cv (nb090_alpha_dummy_021 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_020 A)) (Class.cv (nb090_alpha_dummy_021 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_026 (v : Var) (u : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_023 v u)) (Class.cv (nb090_alpha_dummy_024 v u)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_023 v u)) (Class.cv (nb090_alpha_dummy_024 v u)))).fv) 0)

noncomputable def nb090_alpha_dummy_027 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_020 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_021 A))).fv) 0)

noncomputable def nb090_alpha_dummy_028 (v : Var) (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_023 v u))).fv ∪ ((Class.cv (nb090_alpha_dummy_024 v u))).fv) 0)

noncomputable def nb090_alpha_dummy_029 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_020 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_021 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_030 (v : Var) (u : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_023 v u)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_024 v u)))).fv) 0)

noncomputable def nb090_alpha_dummy_031 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_020 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_020 A))).fv) 0)

noncomputable def nb090_alpha_dummy_032 (v : Var) (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_023 v u))).fv ∪ ((Class.cv (nb090_alpha_dummy_023 v u))).fv) 0)

noncomputable def nb090_alpha_dummy_033 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_021 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_021 A))).fv) 0)

noncomputable def nb090_alpha_dummy_034 (v : Var) (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_024 v u))).fv ∪ ((Class.cv (nb090_alpha_dummy_024 v u))).fv) 0)

noncomputable def nb090_alpha_dummy_035 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_005 A) (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_005 A) (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_036 (v : Var) (u : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_007 v u) (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_007 v u) (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_037 (A : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_038 (v : Var) (u : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_039 (A : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_040 (v : Var) (u : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))).fv) 0)

noncomputable def nb090_alpha_dummy_041 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_042 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) 1)

noncomputable def nb090_alpha_dummy_043 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv h)).fv ∪ ((syn_cfv (syn_c1st) (Class.cv u))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv v))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv u))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv v))).fv) 0)

noncomputable def nb090_alpha_dummy_044 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv h)).fv ∪ ((syn_cfv (syn_c1st) (Class.cv u))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv v))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv u))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv v))).fv) 1)

noncomputable def nb090_alpha_dummy_045 (A : Class) : Var := (freshVar (((syn_cnin (syn_ccom (Class.cv (nb090_alpha_dummy_000 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb090_alpha_dummy_000 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))) (syn_cid))).fv) 0)

noncomputable def nb090_alpha_dummy_046 (h : Var) : Var := (freshVar (((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv) 0)

noncomputable def nb090_alpha_dummy_047 (A : Class) : Var := (freshVar (((syn_ccom (Class.cv (nb090_alpha_dummy_000 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv ∪ ((syn_cid)).fv) 0)

noncomputable def nb090_alpha_dummy_048 (h : Var) : Var := (freshVar (((syn_ccom (Class.cv h) (syn_ccnv (Class.cv h)))).fv ∪ ((syn_cid)).fv) 0)

noncomputable def nb090_alpha_dummy_049 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_050 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) 1)

noncomputable def nb090_alpha_dummy_051 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) 2)

noncomputable def nb090_alpha_dummy_052 (h : Var) : Var := (freshVar (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) 0)

noncomputable def nb090_alpha_dummy_053 (h : Var) : Var := (freshVar (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) 1)

noncomputable def nb090_alpha_dummy_054 (h : Var) : Var := (freshVar (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) 2)

noncomputable def nb090_alpha_dummy_055 (A : Class) : Var := (freshVar (({(nb090_alpha_dummy_049 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_050 A)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_051 A) (syn_wa (syn_wbr (Class.cv (nb090_alpha_dummy_049 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (Class.cv (nb090_alpha_dummy_051 A))) (syn_wbr (Class.cv (nb090_alpha_dummy_051 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_050 A)))))).fv) 0)

noncomputable def nb090_alpha_dummy_056 (h : Var) : Var := (freshVar (({(nb090_alpha_dummy_052 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_053 h)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_054 h) (syn_wa (syn_wbr (Class.cv (nb090_alpha_dummy_052 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb090_alpha_dummy_054 h))) (syn_wbr (Class.cv (nb090_alpha_dummy_054 h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_053 h)))))).fv) 0)

noncomputable def nb090_alpha_dummy_057 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) 0)

noncomputable def nb090_alpha_dummy_058 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) 1)

noncomputable def nb090_alpha_dummy_059 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) 0)

noncomputable def nb090_alpha_dummy_060 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) 1)

noncomputable def nb090_alpha_dummy_061 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_057 A) (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_057 A) (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_050 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_062 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_059 h) (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_059 h) (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_053 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_063 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_057 A) (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_057 A) (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))))).fv) 0)

noncomputable def nb090_alpha_dummy_064 (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_059 h) (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_059 h) (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))))).fv) 0)

noncomputable def nb090_alpha_dummy_065 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_058 A))).fv) 0)

noncomputable def nb090_alpha_dummy_066 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_058 A))).fv) 1)

noncomputable def nb090_alpha_dummy_067 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_060 h))).fv) 0)

noncomputable def nb090_alpha_dummy_068 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_060 h))).fv) 1)

noncomputable def nb090_alpha_dummy_069 (A : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_065 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_065 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_065 A))).fv) 0)

noncomputable def nb090_alpha_dummy_070 (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_067 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_067 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_067 h))).fv) 0)

noncomputable def nb090_alpha_dummy_071 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_072 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_073 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_074 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_075 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_076 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_077 (A : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_072 A)) (Class.cv (nb090_alpha_dummy_073 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_072 A)) (Class.cv (nb090_alpha_dummy_073 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_078 (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_075 h)) (Class.cv (nb090_alpha_dummy_076 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_075 h)) (Class.cv (nb090_alpha_dummy_076 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_079 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_072 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_073 A))).fv) 0)

noncomputable def nb090_alpha_dummy_080 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_075 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_076 h))).fv) 0)

noncomputable def nb090_alpha_dummy_081 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_072 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_073 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_082 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_075 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_076 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_083 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_072 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_072 A))).fv) 0)

noncomputable def nb090_alpha_dummy_084 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_075 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_075 h))).fv) 0)

noncomputable def nb090_alpha_dummy_085 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_073 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_073 A))).fv) 0)

noncomputable def nb090_alpha_dummy_086 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_076 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_076 h))).fv) 0)

noncomputable def nb090_alpha_dummy_087 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_057 A) (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_050 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_057 A) (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_050 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_088 (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_059 h) (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_053 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_059 h) (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_053 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_089 (A : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_090 (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_091 (A : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_092 (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_093 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_051 A))).fv) 0)

noncomputable def nb090_alpha_dummy_094 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_051 A))).fv) 1)

noncomputable def nb090_alpha_dummy_095 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_054 h))).fv) 0)

noncomputable def nb090_alpha_dummy_096 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_054 h))).fv) 1)

noncomputable def nb090_alpha_dummy_097 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_093 A) (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_093 A) (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_051 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_098 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_095 h) (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_095 h) (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_054 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_099 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_093 A) (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_093 A) (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))))).fv) 0)

noncomputable def nb090_alpha_dummy_100 (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_095 h) (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_095 h) (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))))).fv) 0)

noncomputable def nb090_alpha_dummy_101 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_094 A))).fv) 0)

noncomputable def nb090_alpha_dummy_102 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_094 A))).fv) 1)

noncomputable def nb090_alpha_dummy_103 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_096 h))).fv) 0)

noncomputable def nb090_alpha_dummy_104 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_096 h))).fv) 1)

noncomputable def nb090_alpha_dummy_105 (A : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_101 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_101 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_101 A))).fv) 0)

noncomputable def nb090_alpha_dummy_106 (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_103 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_103 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_103 h))).fv) 0)

noncomputable def nb090_alpha_dummy_107 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_108 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_109 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_110 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_111 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_112 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_113 (A : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_108 A)) (Class.cv (nb090_alpha_dummy_109 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_108 A)) (Class.cv (nb090_alpha_dummy_109 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_114 (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_111 h)) (Class.cv (nb090_alpha_dummy_112 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_111 h)) (Class.cv (nb090_alpha_dummy_112 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_115 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_108 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_109 A))).fv) 0)

noncomputable def nb090_alpha_dummy_116 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_111 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_112 h))).fv) 0)

noncomputable def nb090_alpha_dummy_117 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_108 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_109 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_118 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_111 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_112 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_119 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_108 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_108 A))).fv) 0)

noncomputable def nb090_alpha_dummy_120 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_111 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_111 h))).fv) 0)

noncomputable def nb090_alpha_dummy_121 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_109 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_109 A))).fv) 0)

noncomputable def nb090_alpha_dummy_122 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_112 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_112 h))).fv) 0)

noncomputable def nb090_alpha_dummy_123 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_093 A) (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_051 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_093 A) (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_051 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_124 (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_095 h) (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_054 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_095 h) (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_054 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_125 (A : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_126 (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_127 (A : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_128 (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_129 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_000 A))).fv) 0)

noncomputable def nb090_alpha_dummy_130 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_000 A))).fv) 1)

noncomputable def nb090_alpha_dummy_131 (h : Var) : Var := (freshVar (((Class.cv h)).fv) 0)

noncomputable def nb090_alpha_dummy_132 (h : Var) : Var := (freshVar (((Class.cv h)).fv) 1)

noncomputable def nb090_alpha_dummy_133 (A : Class) : Var := (freshVar (({(nb090_alpha_dummy_129 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_130 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_130 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_129 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_134 (h : Var) : Var := (freshVar (({(nb090_alpha_dummy_131 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_132 h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_132 h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_131 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_135 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_130 A))).fv) 0)

noncomputable def nb090_alpha_dummy_136 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_130 A))).fv) 1)

noncomputable def nb090_alpha_dummy_137 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv) 0)

noncomputable def nb090_alpha_dummy_138 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv) 1)

noncomputable def nb090_alpha_dummy_139 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_135 A) (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_135 A) (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_130 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_140 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_137 h) (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_137 h) (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_132 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_141 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_135 A) (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_135 A) (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))))).fv) 0)

noncomputable def nb090_alpha_dummy_142 (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_137 h) (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_137 h) (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))))).fv) 0)

noncomputable def nb090_alpha_dummy_143 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_136 A))).fv) 0)

noncomputable def nb090_alpha_dummy_144 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_136 A))).fv) 1)

noncomputable def nb090_alpha_dummy_145 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_138 h))).fv) 0)

noncomputable def nb090_alpha_dummy_146 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_138 h))).fv) 1)

noncomputable def nb090_alpha_dummy_147 (A : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_143 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_143 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_143 A))).fv) 0)

noncomputable def nb090_alpha_dummy_148 (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_145 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_145 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_145 h))).fv) 0)

noncomputable def nb090_alpha_dummy_149 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
