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

noncomputable def nb057_alpha_dummy_000 : Var := (freshVar ((∅ : Finset Var)) 0)

noncomputable def nb057_alpha_dummy_001 : Var := (freshVar ((∅ : Finset Var)) 1)

noncomputable def nb057_alpha_dummy_002 : Var := (freshVar (({(nb057_alpha_dummy_001)} : Finset Var) ∪ ({(nb057_alpha_dummy_000)} : Finset Var) ∪ ((syn_wfn (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_000)))).fv) 0)

noncomputable def nb057_alpha_dummy_003 (f : Var) (a : Var) : Var := (freshVar (({f} : Finset Var) ∪ ({a} : Finset Var) ∪ ((syn_wfn (Class.cv f) (Class.cv a))).fv) 0)

noncomputable def nb057_alpha_dummy_004 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((Class.cv (nb057_alpha_dummy_000))).fv) 0)

noncomputable def nb057_alpha_dummy_005 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((Class.cv (nb057_alpha_dummy_000))).fv) 1)

noncomputable def nb057_alpha_dummy_006 (f : Var) (a : Var) : Var := (freshVar (((Class.cv f)).fv ∪ ((Class.cv a)).fv) 0)

noncomputable def nb057_alpha_dummy_007 (f : Var) (a : Var) : Var := (freshVar (((Class.cv f)).fv ∪ ((Class.cv a)).fv) 1)

noncomputable def nb057_alpha_dummy_008 : Var := (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cphi (Class.cv (nb057_alpha_dummy_005)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb057_alpha_dummy_009 (f : Var) (a : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb057_alpha_dummy_010 : Var := (freshVar (((Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cphi (Class.cv (nb057_alpha_dummy_005))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cphi (Class.cv (nb057_alpha_dummy_005))))))).fv) 0)

noncomputable def nb057_alpha_dummy_011 (f : Var) (a : Var) : Var := (freshVar (((Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))))))).fv) 0)

noncomputable def nb057_alpha_dummy_012 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_005))).fv) 0)

noncomputable def nb057_alpha_dummy_013 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_005))).fv) 1)

noncomputable def nb057_alpha_dummy_014 (f : Var) (a : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_007 f a))).fv) 0)

noncomputable def nb057_alpha_dummy_015 (f : Var) (a : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_007 f a))).fv) 1)

noncomputable def nb057_alpha_dummy_016 : Var := (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_012)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_012)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_012))).fv) 0)

noncomputable def nb057_alpha_dummy_017 (f : Var) (a : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_014 f a)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_014 f a)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_014 f a))).fv) 0)

noncomputable def nb057_alpha_dummy_018 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb057_alpha_dummy_019 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb057_alpha_dummy_020 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb057_alpha_dummy_021 (f : Var) (a : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb057_alpha_dummy_022 (f : Var) (a : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb057_alpha_dummy_023 (f : Var) (a : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb057_alpha_dummy_024 : Var := (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_019)) (Class.cv (nb057_alpha_dummy_020)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_019)) (Class.cv (nb057_alpha_dummy_020)))).fv) 0)

noncomputable def nb057_alpha_dummy_025 (f : Var) (a : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_022 f a)) (Class.cv (nb057_alpha_dummy_023 f a)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_022 f a)) (Class.cv (nb057_alpha_dummy_023 f a)))).fv) 0)

noncomputable def nb057_alpha_dummy_026 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_019))).fv ∪ ((Class.cv (nb057_alpha_dummy_020))).fv) 0)

noncomputable def nb057_alpha_dummy_027 (f : Var) (a : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_022 f a))).fv ∪ ((Class.cv (nb057_alpha_dummy_023 f a))).fv) 0)

noncomputable def nb057_alpha_dummy_028 : Var := (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_019)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_020)))).fv) 0)

noncomputable def nb057_alpha_dummy_029 (f : Var) (a : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_022 f a)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_023 f a)))).fv) 0)

noncomputable def nb057_alpha_dummy_030 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_019))).fv ∪ ((Class.cv (nb057_alpha_dummy_019))).fv) 0)

noncomputable def nb057_alpha_dummy_031 (f : Var) (a : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_022 f a))).fv ∪ ((Class.cv (nb057_alpha_dummy_022 f a))).fv) 0)

noncomputable def nb057_alpha_dummy_032 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_020))).fv ∪ ((Class.cv (nb057_alpha_dummy_020))).fv) 0)

noncomputable def nb057_alpha_dummy_033 (f : Var) (a : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_023 f a))).fv ∪ ((Class.cv (nb057_alpha_dummy_023 f a))).fv) 0)

noncomputable def nb057_alpha_dummy_034 : Var := (freshVar (((Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb057_alpha_dummy_035 (f : Var) (a : Var) : Var := (freshVar (((Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb057_alpha_dummy_036 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_005))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb057_alpha_dummy_037 (f : Var) (a : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb057_alpha_dummy_038 : Var := (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_005)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_005)))).fv) 0)

noncomputable def nb057_alpha_dummy_039 (f : Var) (a : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))).fv) 0)

noncomputable def nb057_alpha_dummy_040 : Var := (freshVar (((syn_cnin (syn_ccom (Class.cv (nb057_alpha_dummy_001)) (syn_ccnv (Class.cv (nb057_alpha_dummy_001)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb057_alpha_dummy_001)) (syn_ccnv (Class.cv (nb057_alpha_dummy_001)))) (syn_cid))).fv) 0)

noncomputable def nb057_alpha_dummy_041 (f : Var) : Var := (freshVar (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) 0)

noncomputable def nb057_alpha_dummy_042 : Var := (freshVar (((syn_ccom (Class.cv (nb057_alpha_dummy_001)) (syn_ccnv (Class.cv (nb057_alpha_dummy_001))))).fv ∪ ((syn_cid)).fv) 0)

noncomputable def nb057_alpha_dummy_043 (f : Var) : Var := (freshVar (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) 0)

noncomputable def nb057_alpha_dummy_044 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) 0)

noncomputable def nb057_alpha_dummy_045 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) 1)

noncomputable def nb057_alpha_dummy_046 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) 2)

noncomputable def nb057_alpha_dummy_047 (f : Var) : Var := (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 0)

noncomputable def nb057_alpha_dummy_048 (f : Var) : Var := (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 1)

noncomputable def nb057_alpha_dummy_049 (f : Var) : Var := (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 2)

noncomputable def nb057_alpha_dummy_050 : Var := (freshVar (({(nb057_alpha_dummy_044)} : Finset Var) ∪ ({(nb057_alpha_dummy_045)} : Finset Var) ∪ ((syn_wex (nb057_alpha_dummy_046) (syn_wa (syn_wbr (Class.cv (nb057_alpha_dummy_044)) (syn_ccnv (Class.cv (nb057_alpha_dummy_001))) (Class.cv (nb057_alpha_dummy_046))) (syn_wbr (Class.cv (nb057_alpha_dummy_046)) (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_045)))))).fv) 0)

noncomputable def nb057_alpha_dummy_051 (f : Var) : Var := (freshVar (({(nb057_alpha_dummy_047 f)} : Finset Var) ∪ ({(nb057_alpha_dummy_048 f)} : Finset Var) ∪ ((syn_wex (nb057_alpha_dummy_049 f) (syn_wa (syn_wbr (Class.cv (nb057_alpha_dummy_047 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb057_alpha_dummy_049 f))) (syn_wbr (Class.cv (nb057_alpha_dummy_049 f)) (Class.cv f) (Class.cv (nb057_alpha_dummy_048 f)))))).fv) 0)

noncomputable def nb057_alpha_dummy_052 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) 0)

noncomputable def nb057_alpha_dummy_053 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) 1)

noncomputable def nb057_alpha_dummy_054 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) 0)

noncomputable def nb057_alpha_dummy_055 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) 1)

noncomputable def nb057_alpha_dummy_056 : Var := (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cphi (Class.cv (nb057_alpha_dummy_053)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb057_alpha_dummy_057 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb057_alpha_dummy_058 : Var := (freshVar (((Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cphi (Class.cv (nb057_alpha_dummy_053))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cphi (Class.cv (nb057_alpha_dummy_053))))))).fv) 0)

noncomputable def nb057_alpha_dummy_059 (f : Var) : Var := (freshVar (((Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))))))).fv) 0)

noncomputable def nb057_alpha_dummy_060 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_053))).fv) 0)

noncomputable def nb057_alpha_dummy_061 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_053))).fv) 1)

noncomputable def nb057_alpha_dummy_062 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_055 f))).fv) 0)

noncomputable def nb057_alpha_dummy_063 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_055 f))).fv) 1)

noncomputable def nb057_alpha_dummy_064 : Var := (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_060)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_060)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_060))).fv) 0)

noncomputable def nb057_alpha_dummy_065 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_062 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_062 f)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_062 f))).fv) 0)

noncomputable def nb057_alpha_dummy_066 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb057_alpha_dummy_067 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb057_alpha_dummy_068 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb057_alpha_dummy_069 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb057_alpha_dummy_070 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb057_alpha_dummy_071 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb057_alpha_dummy_072 : Var := (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_067)) (Class.cv (nb057_alpha_dummy_068)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_067)) (Class.cv (nb057_alpha_dummy_068)))).fv) 0)

noncomputable def nb057_alpha_dummy_073 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_070 f)) (Class.cv (nb057_alpha_dummy_071 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_070 f)) (Class.cv (nb057_alpha_dummy_071 f)))).fv) 0)

noncomputable def nb057_alpha_dummy_074 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_067))).fv ∪ ((Class.cv (nb057_alpha_dummy_068))).fv) 0)

noncomputable def nb057_alpha_dummy_075 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_070 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_071 f))).fv) 0)

noncomputable def nb057_alpha_dummy_076 : Var := (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_067)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_068)))).fv) 0)

noncomputable def nb057_alpha_dummy_077 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_070 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_071 f)))).fv) 0)

noncomputable def nb057_alpha_dummy_078 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_067))).fv ∪ ((Class.cv (nb057_alpha_dummy_067))).fv) 0)

noncomputable def nb057_alpha_dummy_079 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_070 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_070 f))).fv) 0)

noncomputable def nb057_alpha_dummy_080 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_068))).fv ∪ ((Class.cv (nb057_alpha_dummy_068))).fv) 0)

noncomputable def nb057_alpha_dummy_081 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_071 f))).fv) 0)

noncomputable def nb057_alpha_dummy_082 : Var := (freshVar (((Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb057_alpha_dummy_083 (f : Var) : Var := (freshVar (((Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb057_alpha_dummy_084 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_053))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb057_alpha_dummy_085 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb057_alpha_dummy_086 : Var := (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_053)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_053)))).fv) 0)

noncomputable def nb057_alpha_dummy_087 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))).fv) 0)

noncomputable def nb057_alpha_dummy_088 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_046))).fv) 0)

noncomputable def nb057_alpha_dummy_089 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_046))).fv) 1)

noncomputable def nb057_alpha_dummy_090 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_049 f))).fv) 0)

noncomputable def nb057_alpha_dummy_091 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_049 f))).fv) 1)

noncomputable def nb057_alpha_dummy_092 : Var := (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cphi (Class.cv (nb057_alpha_dummy_089)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb057_alpha_dummy_093 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb057_alpha_dummy_094 : Var := (freshVar (((Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cphi (Class.cv (nb057_alpha_dummy_089))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cphi (Class.cv (nb057_alpha_dummy_089))))))).fv) 0)

noncomputable def nb057_alpha_dummy_095 (f : Var) : Var := (freshVar (((Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))))))).fv) 0)

noncomputable def nb057_alpha_dummy_096 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_089))).fv) 0)

noncomputable def nb057_alpha_dummy_097 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_089))).fv) 1)

noncomputable def nb057_alpha_dummy_098 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_091 f))).fv) 0)

noncomputable def nb057_alpha_dummy_099 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_091 f))).fv) 1)

noncomputable def nb057_alpha_dummy_100 : Var := (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_096)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_096)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_096))).fv) 0)

noncomputable def nb057_alpha_dummy_101 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_098 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_098 f)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_098 f))).fv) 0)

noncomputable def nb057_alpha_dummy_102 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb057_alpha_dummy_103 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb057_alpha_dummy_104 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb057_alpha_dummy_105 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb057_alpha_dummy_106 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb057_alpha_dummy_107 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb057_alpha_dummy_108 : Var := (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_103)) (Class.cv (nb057_alpha_dummy_104)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_103)) (Class.cv (nb057_alpha_dummy_104)))).fv) 0)

noncomputable def nb057_alpha_dummy_109 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_106 f)) (Class.cv (nb057_alpha_dummy_107 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_106 f)) (Class.cv (nb057_alpha_dummy_107 f)))).fv) 0)

noncomputable def nb057_alpha_dummy_110 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_103))).fv ∪ ((Class.cv (nb057_alpha_dummy_104))).fv) 0)

noncomputable def nb057_alpha_dummy_111 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_106 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_107 f))).fv) 0)

noncomputable def nb057_alpha_dummy_112 : Var := (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_103)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_104)))).fv) 0)

noncomputable def nb057_alpha_dummy_113 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_106 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_107 f)))).fv) 0)

noncomputable def nb057_alpha_dummy_114 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_103))).fv ∪ ((Class.cv (nb057_alpha_dummy_103))).fv) 0)

noncomputable def nb057_alpha_dummy_115 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_106 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_106 f))).fv) 0)

noncomputable def nb057_alpha_dummy_116 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_104))).fv ∪ ((Class.cv (nb057_alpha_dummy_104))).fv) 0)

noncomputable def nb057_alpha_dummy_117 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_107 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_107 f))).fv) 0)

noncomputable def nb057_alpha_dummy_118 : Var := (freshVar (((Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb057_alpha_dummy_119 (f : Var) : Var := (freshVar (((Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb057_alpha_dummy_120 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_089))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb057_alpha_dummy_121 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb057_alpha_dummy_122 : Var := (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_089)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_089)))).fv) 0)

noncomputable def nb057_alpha_dummy_123 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))).fv) 0)

noncomputable def nb057_alpha_dummy_124 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_001))).fv) 0)

noncomputable def nb057_alpha_dummy_125 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_001))).fv) 1)

noncomputable def nb057_alpha_dummy_126 (f : Var) : Var := (freshVar (((Class.cv f)).fv) 0)

noncomputable def nb057_alpha_dummy_127 (f : Var) : Var := (freshVar (((Class.cv f)).fv) 1)

noncomputable def nb057_alpha_dummy_128 : Var := (freshVar (({(nb057_alpha_dummy_124)} : Finset Var) ∪ ({(nb057_alpha_dummy_125)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb057_alpha_dummy_125)) (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_124)))).fv) 0)

noncomputable def nb057_alpha_dummy_129 (f : Var) : Var := (freshVar (({(nb057_alpha_dummy_126 f)} : Finset Var) ∪ ({(nb057_alpha_dummy_127 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb057_alpha_dummy_127 f)) (Class.cv f) (Class.cv (nb057_alpha_dummy_126 f)))).fv) 0)

noncomputable def nb057_alpha_dummy_130 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_124))).fv ∪ ((Class.cv (nb057_alpha_dummy_125))).fv) 0)

noncomputable def nb057_alpha_dummy_131 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_124))).fv ∪ ((Class.cv (nb057_alpha_dummy_125))).fv) 1)

noncomputable def nb057_alpha_dummy_132 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_127 f))).fv) 0)

noncomputable def nb057_alpha_dummy_133 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_127 f))).fv) 1)

noncomputable def nb057_alpha_dummy_134 : Var := (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cphi (Class.cv (nb057_alpha_dummy_131)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb057_alpha_dummy_135 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb057_alpha_dummy_136 : Var := (freshVar (((Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cphi (Class.cv (nb057_alpha_dummy_131))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cphi (Class.cv (nb057_alpha_dummy_131))))))).fv) 0)

noncomputable def nb057_alpha_dummy_137 (f : Var) : Var := (freshVar (((Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))))))).fv) 0)

noncomputable def nb057_alpha_dummy_138 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_131))).fv) 0)

noncomputable def nb057_alpha_dummy_139 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_131))).fv) 1)

noncomputable def nb057_alpha_dummy_140 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_133 f))).fv) 0)

noncomputable def nb057_alpha_dummy_141 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_133 f))).fv) 1)

noncomputable def nb057_alpha_dummy_142 : Var := (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_138)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_138)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_138))).fv) 0)

noncomputable def nb057_alpha_dummy_143 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_140 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_140 f)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_140 f))).fv) 0)

noncomputable def nb057_alpha_dummy_144 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb057_alpha_dummy_145 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb057_alpha_dummy_146 : Var := (freshVar (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb057_alpha_dummy_147 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb057_alpha_dummy_148 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb057_alpha_dummy_149 (f : Var) : Var := (freshVar (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) 2)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
