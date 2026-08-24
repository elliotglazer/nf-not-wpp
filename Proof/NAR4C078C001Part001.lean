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

noncomputable def nb078_alpha_dummy_000 : Var := (freshVar ((∅ : Finset Var)) 0)

noncomputable def nb078_alpha_dummy_001 : Var := (freshVar ((∅ : Finset Var)) 1)

noncomputable def nb078_alpha_dummy_002 : Var := (freshVar ((∅ : Finset Var)) 2)

noncomputable def nb078_alpha_dummy_003 : Var := (freshVar ((∅ : Finset Var)) 3)

noncomputable def nb078_alpha_dummy_004 : Var := (freshVar ((∅ : Finset Var)) 4)

noncomputable def nb078_alpha_dummy_005 : Var := (freshVar (((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_000)) (syn_ccnv (Class.cv (nb078_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_000)) (syn_ccnv (Class.cv (nb078_alpha_dummy_000)))) (syn_cid))).fv) 0)

noncomputable def nb078_alpha_dummy_006 (f : Var) : Var := (freshVar (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) 0)

noncomputable def nb078_alpha_dummy_007 : Var := (freshVar (((syn_ccom (Class.cv (nb078_alpha_dummy_000)) (syn_ccnv (Class.cv (nb078_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) 0)

noncomputable def nb078_alpha_dummy_008 (f : Var) : Var := (freshVar (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) 0)

noncomputable def nb078_alpha_dummy_009 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) 0)

noncomputable def nb078_alpha_dummy_010 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) 1)

noncomputable def nb078_alpha_dummy_011 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) 2)

noncomputable def nb078_alpha_dummy_012 (f : Var) : Var := (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 0)

noncomputable def nb078_alpha_dummy_013 (f : Var) : Var := (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 1)

noncomputable def nb078_alpha_dummy_014 (f : Var) : Var := (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 2)

noncomputable def nb078_alpha_dummy_015 : Var := (freshVar (({(nb078_alpha_dummy_009)} : Finset Var) ∪ ({(nb078_alpha_dummy_010)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_011) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_009)) (syn_ccnv (Class.cv (nb078_alpha_dummy_000))) (Class.cv (nb078_alpha_dummy_011))) (syn_wbr (Class.cv (nb078_alpha_dummy_011)) (Class.cv (nb078_alpha_dummy_000)) (Class.cv (nb078_alpha_dummy_010)))))).fv) 0)

noncomputable def nb078_alpha_dummy_016 (f : Var) : Var := (freshVar (({(nb078_alpha_dummy_012 f)} : Finset Var) ∪ ({(nb078_alpha_dummy_013 f)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_014 f) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_012 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb078_alpha_dummy_014 f))) (syn_wbr (Class.cv (nb078_alpha_dummy_014 f)) (Class.cv f) (Class.cv (nb078_alpha_dummy_013 f)))))).fv) 0)

noncomputable def nb078_alpha_dummy_017 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) 0)

noncomputable def nb078_alpha_dummy_018 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) 1)

noncomputable def nb078_alpha_dummy_019 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) 0)

noncomputable def nb078_alpha_dummy_020 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) 1)

noncomputable def nb078_alpha_dummy_021 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_017) (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_009)) (Wff.classEq (Class.cv (nb078_alpha_dummy_017)) (syn_cphi (Class.cv (nb078_alpha_dummy_018)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_017) (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_010)) (Wff.classEq (Class.cv (nb078_alpha_dummy_017)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_018))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_022 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_019 f) (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_012 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_019 f) (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_013 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_023 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_017) (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_009)) (Wff.classEq (Class.cv (nb078_alpha_dummy_017)) (syn_cphi (Class.cv (nb078_alpha_dummy_018))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_017) (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_009)) (Wff.classEq (Class.cv (nb078_alpha_dummy_017)) (syn_cphi (Class.cv (nb078_alpha_dummy_018))))))).fv) 0)

noncomputable def nb078_alpha_dummy_024 (f : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_019 f) (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_012 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_019 f) (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_012 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))))))).fv) 0)

noncomputable def nb078_alpha_dummy_025 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_018))).fv) 0)

noncomputable def nb078_alpha_dummy_026 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_018))).fv) 1)

noncomputable def nb078_alpha_dummy_027 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_020 f))).fv) 0)

noncomputable def nb078_alpha_dummy_028 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_020 f))).fv) 1)

noncomputable def nb078_alpha_dummy_029 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_025)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_025)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_025))).fv) 0)

noncomputable def nb078_alpha_dummy_030 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_027 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_027 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_027 f))).fv) 0)

noncomputable def nb078_alpha_dummy_031 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_032 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_033 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_034 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_035 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_036 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_037 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_032)) (Class.cv (nb078_alpha_dummy_033)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_032)) (Class.cv (nb078_alpha_dummy_033)))).fv) 0)

noncomputable def nb078_alpha_dummy_038 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_035 f)) (Class.cv (nb078_alpha_dummy_036 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_035 f)) (Class.cv (nb078_alpha_dummy_036 f)))).fv) 0)

noncomputable def nb078_alpha_dummy_039 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_032))).fv ∪ ((Class.cv (nb078_alpha_dummy_033))).fv) 0)

noncomputable def nb078_alpha_dummy_040 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_035 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_036 f))).fv) 0)

noncomputable def nb078_alpha_dummy_041 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_032)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_033)))).fv) 0)

noncomputable def nb078_alpha_dummy_042 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_035 f)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_036 f)))).fv) 0)

noncomputable def nb078_alpha_dummy_043 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_032))).fv ∪ ((Class.cv (nb078_alpha_dummy_032))).fv) 0)

noncomputable def nb078_alpha_dummy_044 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_035 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_035 f))).fv) 0)

noncomputable def nb078_alpha_dummy_045 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_033))).fv ∪ ((Class.cv (nb078_alpha_dummy_033))).fv) 0)

noncomputable def nb078_alpha_dummy_046 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_036 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_036 f))).fv) 0)

noncomputable def nb078_alpha_dummy_047 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_017) (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_010)) (Wff.classEq (Class.cv (nb078_alpha_dummy_017)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_018))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_017) (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_010)) (Wff.classEq (Class.cv (nb078_alpha_dummy_017)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_018))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_048 (f : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_019 f) (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_013 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_019 f) (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_013 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_049 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_018))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_050 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_051 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_018)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_018)))).fv) 0)

noncomputable def nb078_alpha_dummy_052 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))).fv) 0)

noncomputable def nb078_alpha_dummy_053 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_011))).fv) 0)

noncomputable def nb078_alpha_dummy_054 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_011))).fv) 1)

noncomputable def nb078_alpha_dummy_055 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_014 f))).fv) 0)

noncomputable def nb078_alpha_dummy_056 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_014 f))).fv) 1)

noncomputable def nb078_alpha_dummy_057 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_053) (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_009)) (Wff.classEq (Class.cv (nb078_alpha_dummy_053)) (syn_cphi (Class.cv (nb078_alpha_dummy_054)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_053) (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_011)) (Wff.classEq (Class.cv (nb078_alpha_dummy_053)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_054))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_058 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_055 f) (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_012 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_055 f) (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_014 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_059 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_053) (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_009)) (Wff.classEq (Class.cv (nb078_alpha_dummy_053)) (syn_cphi (Class.cv (nb078_alpha_dummy_054))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_053) (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_009)) (Wff.classEq (Class.cv (nb078_alpha_dummy_053)) (syn_cphi (Class.cv (nb078_alpha_dummy_054))))))).fv) 0)

noncomputable def nb078_alpha_dummy_060 (f : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_055 f) (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_012 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_055 f) (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_012 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))))))).fv) 0)

noncomputable def nb078_alpha_dummy_061 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_054))).fv) 0)

noncomputable def nb078_alpha_dummy_062 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_054))).fv) 1)

noncomputable def nb078_alpha_dummy_063 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_056 f))).fv) 0)

noncomputable def nb078_alpha_dummy_064 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_056 f))).fv) 1)

noncomputable def nb078_alpha_dummy_065 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_061)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_061)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_061))).fv) 0)

noncomputable def nb078_alpha_dummy_066 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_063 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_063 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_063 f))).fv) 0)

noncomputable def nb078_alpha_dummy_067 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_068 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_069 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_070 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_071 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_072 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_073 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_068)) (Class.cv (nb078_alpha_dummy_069)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_068)) (Class.cv (nb078_alpha_dummy_069)))).fv) 0)

noncomputable def nb078_alpha_dummy_074 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_071 f)) (Class.cv (nb078_alpha_dummy_072 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_071 f)) (Class.cv (nb078_alpha_dummy_072 f)))).fv) 0)

noncomputable def nb078_alpha_dummy_075 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_068))).fv ∪ ((Class.cv (nb078_alpha_dummy_069))).fv) 0)

noncomputable def nb078_alpha_dummy_076 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_072 f))).fv) 0)

noncomputable def nb078_alpha_dummy_077 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_068)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_069)))).fv) 0)

noncomputable def nb078_alpha_dummy_078 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_071 f)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_072 f)))).fv) 0)

noncomputable def nb078_alpha_dummy_079 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_068))).fv ∪ ((Class.cv (nb078_alpha_dummy_068))).fv) 0)

noncomputable def nb078_alpha_dummy_080 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_071 f))).fv) 0)

noncomputable def nb078_alpha_dummy_081 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_069))).fv ∪ ((Class.cv (nb078_alpha_dummy_069))).fv) 0)

noncomputable def nb078_alpha_dummy_082 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_072 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_072 f))).fv) 0)

noncomputable def nb078_alpha_dummy_083 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_053) (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_011)) (Wff.classEq (Class.cv (nb078_alpha_dummy_053)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_054))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_053) (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_011)) (Wff.classEq (Class.cv (nb078_alpha_dummy_053)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_054))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_084 (f : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_055 f) (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_014 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_055 f) (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_014 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_085 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_054))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_086 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_087 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_054)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_054)))).fv) 0)

noncomputable def nb078_alpha_dummy_088 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))).fv) 0)

noncomputable def nb078_alpha_dummy_089 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_000))).fv) 0)

noncomputable def nb078_alpha_dummy_090 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_000))).fv) 1)

noncomputable def nb078_alpha_dummy_091 (f : Var) : Var := (freshVar (((Class.cv f)).fv) 0)

noncomputable def nb078_alpha_dummy_092 (f : Var) : Var := (freshVar (((Class.cv f)).fv) 1)

noncomputable def nb078_alpha_dummy_093 : Var := (freshVar (({(nb078_alpha_dummy_089)} : Finset Var) ∪ ({(nb078_alpha_dummy_090)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_090)) (Class.cv (nb078_alpha_dummy_000)) (Class.cv (nb078_alpha_dummy_089)))).fv) 0)

noncomputable def nb078_alpha_dummy_094 (f : Var) : Var := (freshVar (({(nb078_alpha_dummy_091 f)} : Finset Var) ∪ ({(nb078_alpha_dummy_092 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_092 f)) (Class.cv f) (Class.cv (nb078_alpha_dummy_091 f)))).fv) 0)

noncomputable def nb078_alpha_dummy_095 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_089))).fv ∪ ((Class.cv (nb078_alpha_dummy_090))).fv) 0)

noncomputable def nb078_alpha_dummy_096 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_089))).fv ∪ ((Class.cv (nb078_alpha_dummy_090))).fv) 1)

noncomputable def nb078_alpha_dummy_097 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_091 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_092 f))).fv) 0)

noncomputable def nb078_alpha_dummy_098 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_091 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_092 f))).fv) 1)

noncomputable def nb078_alpha_dummy_099 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_095) (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_089)) (Wff.classEq (Class.cv (nb078_alpha_dummy_095)) (syn_cphi (Class.cv (nb078_alpha_dummy_096)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_095) (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_090)) (Wff.classEq (Class.cv (nb078_alpha_dummy_095)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_096))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_100 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_097 f) (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_091 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_097 f) (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_092 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_101 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_095) (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_089)) (Wff.classEq (Class.cv (nb078_alpha_dummy_095)) (syn_cphi (Class.cv (nb078_alpha_dummy_096))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_095) (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_089)) (Wff.classEq (Class.cv (nb078_alpha_dummy_095)) (syn_cphi (Class.cv (nb078_alpha_dummy_096))))))).fv) 0)

noncomputable def nb078_alpha_dummy_102 (f : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_097 f) (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_091 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_097 f) (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_091 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))))))).fv) 0)

noncomputable def nb078_alpha_dummy_103 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_096))).fv) 0)

noncomputable def nb078_alpha_dummy_104 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_096))).fv) 1)

noncomputable def nb078_alpha_dummy_105 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_098 f))).fv) 0)

noncomputable def nb078_alpha_dummy_106 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_098 f))).fv) 1)

noncomputable def nb078_alpha_dummy_107 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_103)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_103)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_103))).fv) 0)

noncomputable def nb078_alpha_dummy_108 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_105 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_105 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_105 f))).fv) 0)

noncomputable def nb078_alpha_dummy_109 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_110 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_111 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_112 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_113 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_114 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_115 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_110)) (Class.cv (nb078_alpha_dummy_111)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_110)) (Class.cv (nb078_alpha_dummy_111)))).fv) 0)

noncomputable def nb078_alpha_dummy_116 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_113 f)) (Class.cv (nb078_alpha_dummy_114 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_113 f)) (Class.cv (nb078_alpha_dummy_114 f)))).fv) 0)

noncomputable def nb078_alpha_dummy_117 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_110))).fv ∪ ((Class.cv (nb078_alpha_dummy_111))).fv) 0)

noncomputable def nb078_alpha_dummy_118 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_113 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_114 f))).fv) 0)

noncomputable def nb078_alpha_dummy_119 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_110)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_111)))).fv) 0)

noncomputable def nb078_alpha_dummy_120 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_113 f)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_114 f)))).fv) 0)

noncomputable def nb078_alpha_dummy_121 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_110))).fv ∪ ((Class.cv (nb078_alpha_dummy_110))).fv) 0)

noncomputable def nb078_alpha_dummy_122 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_113 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_113 f))).fv) 0)

noncomputable def nb078_alpha_dummy_123 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_111))).fv ∪ ((Class.cv (nb078_alpha_dummy_111))).fv) 0)

noncomputable def nb078_alpha_dummy_124 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_114 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_114 f))).fv) 0)

noncomputable def nb078_alpha_dummy_125 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_095) (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_090)) (Wff.classEq (Class.cv (nb078_alpha_dummy_095)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_096))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_095) (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_090)) (Wff.classEq (Class.cv (nb078_alpha_dummy_095)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_096))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_126 (f : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_097 f) (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_092 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_097 f) (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_092 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_127 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_096))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_128 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_129 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_096)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_096)))).fv) 0)

noncomputable def nb078_alpha_dummy_130 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))).fv) 0)

noncomputable def nb078_alpha_dummy_131 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_090))).fv ∪ ((Class.cv (nb078_alpha_dummy_089))).fv) 0)

noncomputable def nb078_alpha_dummy_132 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_090))).fv ∪ ((Class.cv (nb078_alpha_dummy_089))).fv) 1)

noncomputable def nb078_alpha_dummy_133 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_092 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_091 f))).fv) 0)

noncomputable def nb078_alpha_dummy_134 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_092 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_091 f))).fv) 1)

noncomputable def nb078_alpha_dummy_135 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_131) (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_090)) (Wff.classEq (Class.cv (nb078_alpha_dummy_131)) (syn_cphi (Class.cv (nb078_alpha_dummy_132)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_131) (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_089)) (Wff.classEq (Class.cv (nb078_alpha_dummy_131)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_132))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_136 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_133 f) (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_092 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_133 f) (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_091 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_137 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_131) (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_090)) (Wff.classEq (Class.cv (nb078_alpha_dummy_131)) (syn_cphi (Class.cv (nb078_alpha_dummy_132))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_131) (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_090)) (Wff.classEq (Class.cv (nb078_alpha_dummy_131)) (syn_cphi (Class.cv (nb078_alpha_dummy_132))))))).fv) 0)

noncomputable def nb078_alpha_dummy_138 (f : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_133 f) (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_092 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_133 f) (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_092 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))))))).fv) 0)

noncomputable def nb078_alpha_dummy_139 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_132))).fv) 0)

noncomputable def nb078_alpha_dummy_140 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_132))).fv) 1)

noncomputable def nb078_alpha_dummy_141 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_134 f))).fv) 0)

noncomputable def nb078_alpha_dummy_142 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_134 f))).fv) 1)

noncomputable def nb078_alpha_dummy_143 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_139)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_139)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_139))).fv) 0)

noncomputable def nb078_alpha_dummy_144 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_141 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_141 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_141 f))).fv) 0)

noncomputable def nb078_alpha_dummy_145 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_146 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_147 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_148 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_149 (f : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) 1)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
