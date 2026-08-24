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

noncomputable def nb076_alpha_dummy_000 : Var := (freshVar ((∅ : Finset Var)) 0)

noncomputable def nb076_alpha_dummy_001 : Var := (freshVar ((∅ : Finset Var)) 1)

noncomputable def nb076_alpha_dummy_002 : Var := (freshVar ((∅ : Finset Var)) 2)

noncomputable def nb076_alpha_dummy_003 : Var := (freshVar ((∅ : Finset Var)) 3)

noncomputable def nb076_alpha_dummy_004 : Var := (freshVar ((∅ : Finset Var)) 4)

noncomputable def nb076_alpha_dummy_005 : Var := (freshVar (({(nb076_alpha_dummy_003)} : Finset Var) ∪ ((syn_cncs)).fv ∪ ({(nb076_alpha_dummy_004)} : Finset Var) ∪ ((syn_cncs)).fv ∪ ((Class.cab (nb076_alpha_dummy_000) (syn_wrex (nb076_alpha_dummy_001) (Class.cv (nb076_alpha_dummy_003)) (syn_wrex (nb076_alpha_dummy_002) (Class.cv (nb076_alpha_dummy_004)) (syn_wbr (Class.cv (nb076_alpha_dummy_000)) (syn_cen) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))))))).fv) 0)

noncomputable def nb076_alpha_dummy_006 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : Var := (freshVar (({m} : Finset Var) ∪ ((syn_cncs)).fv ∪ ({n} : Finset Var) ∪ ((syn_cncs)).fv ∪ ((Class.cab a (syn_wrex b (Class.cv m) (syn_wrex g (Class.cv n) (syn_wbr (Class.cv a) (syn_cen) (syn_cxp (Class.cv b) (Class.cv g))))))).fv) 0)

noncomputable def nb076_alpha_dummy_007 : Var := (freshVar (({(nb076_alpha_dummy_003)} : Finset Var) ∪ ({(nb076_alpha_dummy_004)} : Finset Var) ∪ ({(nb076_alpha_dummy_005)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_003)) (syn_cncs)) (Wff.classMem (Class.cv (nb076_alpha_dummy_004)) (syn_cncs))) (Wff.classEq (Class.cv (nb076_alpha_dummy_005)) (Class.cab (nb076_alpha_dummy_000) (syn_wrex (nb076_alpha_dummy_001) (Class.cv (nb076_alpha_dummy_003)) (syn_wrex (nb076_alpha_dummy_002) (Class.cv (nb076_alpha_dummy_004)) (syn_wbr (Class.cv (nb076_alpha_dummy_000)) (syn_cen) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))))))))).fv) 0)

noncomputable def nb076_alpha_dummy_008 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : Var := (freshVar (({m} : Finset Var) ∪ ({n} : Finset Var) ∪ ({(nb076_alpha_dummy_006 g m n a b)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv m) (syn_cncs)) (Wff.classMem (Class.cv n) (syn_cncs))) (Wff.classEq (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Class.cab a (syn_wrex b (Class.cv m) (syn_wrex g (Class.cv n) (syn_wbr (Class.cv a) (syn_cen) (syn_cxp (Class.cv b) (Class.cv g))))))))).fv) 0)

noncomputable def nb076_alpha_dummy_009 : Var := (freshVar (((syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))).fv ∪ ((Class.cv (nb076_alpha_dummy_005))).fv) 0)

noncomputable def nb076_alpha_dummy_010 : Var := (freshVar (((syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))).fv ∪ ((Class.cv (nb076_alpha_dummy_005))).fv) 1)

noncomputable def nb076_alpha_dummy_011 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : Var := (freshVar (((syn_cop (Class.cv m) (Class.cv n))).fv ∪ ((Class.cv (nb076_alpha_dummy_006 g m n a b))).fv) 0)

noncomputable def nb076_alpha_dummy_012 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : Var := (freshVar (((syn_cop (Class.cv m) (Class.cv n))).fv ∪ ((Class.cv (nb076_alpha_dummy_006 g m n a b))).fv) 1)

noncomputable def nb076_alpha_dummy_013 : Var := (freshVar (((syn_ccompl (Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004))) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cphi (Class.cv (nb076_alpha_dummy_010)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005)) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb076_alpha_dummy_014 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb076_alpha_dummy_015 : Var := (freshVar (((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004))) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cphi (Class.cv (nb076_alpha_dummy_010))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004))) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cphi (Class.cv (nb076_alpha_dummy_010))))))).fv) 0)

noncomputable def nb076_alpha_dummy_016 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : Var := (freshVar (((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))))).fv) 0)

noncomputable def nb076_alpha_dummy_017 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_003))).fv ∪ ((Class.cv (nb076_alpha_dummy_004))).fv) 0)

noncomputable def nb076_alpha_dummy_018 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_003))).fv ∪ ((Class.cv (nb076_alpha_dummy_004))).fv) 1)

noncomputable def nb076_alpha_dummy_019 (m : Var) (n : Var) : Var := (freshVar (((Class.cv m)).fv ∪ ((Class.cv n)).fv) 0)

noncomputable def nb076_alpha_dummy_020 (m : Var) (n : Var) : Var := (freshVar (((Class.cv m)).fv ∪ ((Class.cv n)).fv) 1)

noncomputable def nb076_alpha_dummy_021 : Var := (freshVar (((syn_ccompl (Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cphi (Class.cv (nb076_alpha_dummy_018)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb076_alpha_dummy_022 (m : Var) (n : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb076_alpha_dummy_023 : Var := (freshVar (((Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cphi (Class.cv (nb076_alpha_dummy_018))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cphi (Class.cv (nb076_alpha_dummy_018))))))).fv) 0)

noncomputable def nb076_alpha_dummy_024 (m : Var) (n : Var) : Var := (freshVar (((Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))))).fv) 0)

noncomputable def nb076_alpha_dummy_025 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_018))).fv) 0)

noncomputable def nb076_alpha_dummy_026 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_018))).fv) 1)

noncomputable def nb076_alpha_dummy_027 (m : Var) (n : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_020 m n))).fv) 0)

noncomputable def nb076_alpha_dummy_028 (m : Var) (n : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_020 m n))).fv) 1)

noncomputable def nb076_alpha_dummy_029 : Var := (freshVar (((Wff.classMem (Class.cv (nb076_alpha_dummy_025)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_025)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_025))).fv) 0)

noncomputable def nb076_alpha_dummy_030 (m : Var) (n : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb076_alpha_dummy_027 m n)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_027 m n)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_027 m n))).fv) 0)

noncomputable def nb076_alpha_dummy_031 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb076_alpha_dummy_032 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb076_alpha_dummy_033 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb076_alpha_dummy_034 (m : Var) (n : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb076_alpha_dummy_035 (m : Var) (n : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb076_alpha_dummy_036 (m : Var) (n : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb076_alpha_dummy_037 : Var := (freshVar (((syn_cnin (Class.cv (nb076_alpha_dummy_032)) (Class.cv (nb076_alpha_dummy_033)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_032)) (Class.cv (nb076_alpha_dummy_033)))).fv) 0)

noncomputable def nb076_alpha_dummy_038 (m : Var) (n : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb076_alpha_dummy_035 m n)) (Class.cv (nb076_alpha_dummy_036 m n)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_035 m n)) (Class.cv (nb076_alpha_dummy_036 m n)))).fv) 0)

noncomputable def nb076_alpha_dummy_039 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_032))).fv ∪ ((Class.cv (nb076_alpha_dummy_033))).fv) 0)

noncomputable def nb076_alpha_dummy_040 (m : Var) (n : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_035 m n))).fv ∪ ((Class.cv (nb076_alpha_dummy_036 m n))).fv) 0)

noncomputable def nb076_alpha_dummy_041 : Var := (freshVar (((syn_ccompl (Class.cv (nb076_alpha_dummy_032)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_033)))).fv) 0)

noncomputable def nb076_alpha_dummy_042 (m : Var) (n : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb076_alpha_dummy_035 m n)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_036 m n)))).fv) 0)

noncomputable def nb076_alpha_dummy_043 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_032))).fv ∪ ((Class.cv (nb076_alpha_dummy_032))).fv) 0)

noncomputable def nb076_alpha_dummy_044 (m : Var) (n : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_035 m n))).fv ∪ ((Class.cv (nb076_alpha_dummy_035 m n))).fv) 0)

noncomputable def nb076_alpha_dummy_045 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_033))).fv ∪ ((Class.cv (nb076_alpha_dummy_033))).fv) 0)

noncomputable def nb076_alpha_dummy_046 (m : Var) (n : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_036 m n))).fv ∪ ((Class.cv (nb076_alpha_dummy_036 m n))).fv) 0)

noncomputable def nb076_alpha_dummy_047 : Var := (freshVar (((Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb076_alpha_dummy_048 (m : Var) (n : Var) : Var := (freshVar (((Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb076_alpha_dummy_049 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_018))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb076_alpha_dummy_050 (m : Var) (n : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb076_alpha_dummy_051 : Var := (freshVar (((syn_cphi (Class.cv (nb076_alpha_dummy_018)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_018)))).fv) 0)

noncomputable def nb076_alpha_dummy_052 (m : Var) (n : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))).fv) 0)

noncomputable def nb076_alpha_dummy_053 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_010))).fv) 0)

noncomputable def nb076_alpha_dummy_054 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_010))).fv) 1)

noncomputable def nb076_alpha_dummy_055 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_012 g m n a b))).fv) 0)

noncomputable def nb076_alpha_dummy_056 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_012 g m n a b))).fv) 1)

noncomputable def nb076_alpha_dummy_057 : Var := (freshVar (((Wff.classMem (Class.cv (nb076_alpha_dummy_053)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_053)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_053))).fv) 0)

noncomputable def nb076_alpha_dummy_058 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb076_alpha_dummy_055 g m n a b)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_055 g m n a b)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv) 0)

noncomputable def nb076_alpha_dummy_059 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb076_alpha_dummy_060 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb076_alpha_dummy_061 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb076_alpha_dummy_062 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb076_alpha_dummy_063 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb076_alpha_dummy_064 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb076_alpha_dummy_065 : Var := (freshVar (((syn_cnin (Class.cv (nb076_alpha_dummy_060)) (Class.cv (nb076_alpha_dummy_061)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_060)) (Class.cv (nb076_alpha_dummy_061)))).fv) 0)

noncomputable def nb076_alpha_dummy_066 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb076_alpha_dummy_063 g m n a b)) (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_063 g m n a b)) (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv) 0)

noncomputable def nb076_alpha_dummy_067 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_060))).fv ∪ ((Class.cv (nb076_alpha_dummy_061))).fv) 0)

noncomputable def nb076_alpha_dummy_068 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv) 0)

noncomputable def nb076_alpha_dummy_069 : Var := (freshVar (((syn_ccompl (Class.cv (nb076_alpha_dummy_060)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_061)))).fv) 0)

noncomputable def nb076_alpha_dummy_070 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb076_alpha_dummy_063 g m n a b)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv) 0)

noncomputable def nb076_alpha_dummy_071 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_060))).fv ∪ ((Class.cv (nb076_alpha_dummy_060))).fv) 0)

noncomputable def nb076_alpha_dummy_072 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv) 0)

noncomputable def nb076_alpha_dummy_073 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_061))).fv ∪ ((Class.cv (nb076_alpha_dummy_061))).fv) 0)

noncomputable def nb076_alpha_dummy_074 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv) 0)

noncomputable def nb076_alpha_dummy_075 : Var := (freshVar (((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005)) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005)) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb076_alpha_dummy_076 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : Var := (freshVar (((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb076_alpha_dummy_077 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_010))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb076_alpha_dummy_078 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb076_alpha_dummy_079 : Var := (freshVar (((syn_cphi (Class.cv (nb076_alpha_dummy_010)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_010)))).fv) 0)

noncomputable def nb076_alpha_dummy_080 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))).fv) 0)

noncomputable def nb076_alpha_dummy_081 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_000))).fv ∪ ((syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))).fv) 0)

noncomputable def nb076_alpha_dummy_082 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_000))).fv ∪ ((syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))).fv) 1)

noncomputable def nb076_alpha_dummy_083 (g : Var) (a : Var) (b : Var) : Var := (freshVar (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv) 0)

noncomputable def nb076_alpha_dummy_084 (g : Var) (a : Var) (b : Var) : Var := (freshVar (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv) 1)

noncomputable def nb076_alpha_dummy_085 : Var := (freshVar (((syn_ccompl (Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000)) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cphi (Class.cv (nb076_alpha_dummy_082)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002))) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb076_alpha_dummy_086 (g : Var) (a : Var) (b : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g)) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb076_alpha_dummy_087 : Var := (freshVar (((Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000)) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cphi (Class.cv (nb076_alpha_dummy_082))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000)) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cphi (Class.cv (nb076_alpha_dummy_082))))))).fv) 0)

noncomputable def nb076_alpha_dummy_088 (g : Var) (a : Var) (b : Var) : Var := (freshVar (((Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))))).fv) 0)

noncomputable def nb076_alpha_dummy_089 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_082))).fv) 0)

noncomputable def nb076_alpha_dummy_090 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_082))).fv) 1)

noncomputable def nb076_alpha_dummy_091 (g : Var) (a : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_084 g a b))).fv) 0)

noncomputable def nb076_alpha_dummy_092 (g : Var) (a : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_084 g a b))).fv) 1)

noncomputable def nb076_alpha_dummy_093 : Var := (freshVar (((Wff.classMem (Class.cv (nb076_alpha_dummy_089)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_089)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_089))).fv) 0)

noncomputable def nb076_alpha_dummy_094 (g : Var) (a : Var) (b : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb076_alpha_dummy_091 g a b)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_091 g a b)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_091 g a b))).fv) 0)

noncomputable def nb076_alpha_dummy_095 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb076_alpha_dummy_096 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb076_alpha_dummy_097 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb076_alpha_dummy_098 (g : Var) (a : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb076_alpha_dummy_099 (g : Var) (a : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb076_alpha_dummy_100 (g : Var) (a : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb076_alpha_dummy_101 : Var := (freshVar (((syn_cnin (Class.cv (nb076_alpha_dummy_096)) (Class.cv (nb076_alpha_dummy_097)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_096)) (Class.cv (nb076_alpha_dummy_097)))).fv) 0)

noncomputable def nb076_alpha_dummy_102 (g : Var) (a : Var) (b : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb076_alpha_dummy_099 g a b)) (Class.cv (nb076_alpha_dummy_100 g a b)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_099 g a b)) (Class.cv (nb076_alpha_dummy_100 g a b)))).fv) 0)

noncomputable def nb076_alpha_dummy_103 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_096))).fv ∪ ((Class.cv (nb076_alpha_dummy_097))).fv) 0)

noncomputable def nb076_alpha_dummy_104 (g : Var) (a : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_099 g a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_100 g a b))).fv) 0)

noncomputable def nb076_alpha_dummy_105 : Var := (freshVar (((syn_ccompl (Class.cv (nb076_alpha_dummy_096)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_097)))).fv) 0)

noncomputable def nb076_alpha_dummy_106 (g : Var) (a : Var) (b : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb076_alpha_dummy_099 g a b)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_100 g a b)))).fv) 0)

noncomputable def nb076_alpha_dummy_107 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_096))).fv ∪ ((Class.cv (nb076_alpha_dummy_096))).fv) 0)

noncomputable def nb076_alpha_dummy_108 (g : Var) (a : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_099 g a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_099 g a b))).fv) 0)

noncomputable def nb076_alpha_dummy_109 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_097))).fv ∪ ((Class.cv (nb076_alpha_dummy_097))).fv) 0)

noncomputable def nb076_alpha_dummy_110 (g : Var) (a : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_100 g a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_100 g a b))).fv) 0)

noncomputable def nb076_alpha_dummy_111 : Var := (freshVar (((Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002))) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002))) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb076_alpha_dummy_112 (g : Var) (a : Var) (b : Var) : Var := (freshVar (((Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g)) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g)) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb076_alpha_dummy_113 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_001))).fv ∪ ((Class.cv (nb076_alpha_dummy_002))).fv) 0)

noncomputable def nb076_alpha_dummy_114 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_001))).fv ∪ ((Class.cv (nb076_alpha_dummy_002))).fv) 1)

noncomputable def nb076_alpha_dummy_115 (g : Var) (b : Var) : Var := (freshVar (((Class.cv b)).fv ∪ ((Class.cv g)).fv) 0)

noncomputable def nb076_alpha_dummy_116 (g : Var) (b : Var) : Var := (freshVar (((Class.cv b)).fv ∪ ((Class.cv g)).fv) 1)

noncomputable def nb076_alpha_dummy_117 : Var := (freshVar (({(nb076_alpha_dummy_113)} : Finset Var) ∪ ({(nb076_alpha_dummy_114)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_113)) (Class.cv (nb076_alpha_dummy_001))) (Wff.classMem (Class.cv (nb076_alpha_dummy_114)) (Class.cv (nb076_alpha_dummy_002))))).fv) 0)

noncomputable def nb076_alpha_dummy_118 (g : Var) (b : Var) : Var := (freshVar (({(nb076_alpha_dummy_115 g b)} : Finset Var) ∪ ({(nb076_alpha_dummy_116 g b)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_115 g b)) (Class.cv b)) (Wff.classMem (Class.cv (nb076_alpha_dummy_116 g b)) (Class.cv g)))).fv) 0)

noncomputable def nb076_alpha_dummy_119 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_113))).fv ∪ ((Class.cv (nb076_alpha_dummy_114))).fv) 0)

noncomputable def nb076_alpha_dummy_120 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_113))).fv ∪ ((Class.cv (nb076_alpha_dummy_114))).fv) 1)

noncomputable def nb076_alpha_dummy_121 (g : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_115 g b))).fv ∪ ((Class.cv (nb076_alpha_dummy_116 g b))).fv) 0)

noncomputable def nb076_alpha_dummy_122 (g : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_115 g b))).fv ∪ ((Class.cv (nb076_alpha_dummy_116 g b))).fv) 1)

noncomputable def nb076_alpha_dummy_123 : Var := (freshVar (((syn_ccompl (Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cphi (Class.cv (nb076_alpha_dummy_120)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb076_alpha_dummy_124 (g : Var) (b : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb076_alpha_dummy_125 : Var := (freshVar (((Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cphi (Class.cv (nb076_alpha_dummy_120))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cphi (Class.cv (nb076_alpha_dummy_120))))))).fv) 0)

noncomputable def nb076_alpha_dummy_126 (g : Var) (b : Var) : Var := (freshVar (((Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))))).fv) 0)

noncomputable def nb076_alpha_dummy_127 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_120))).fv) 0)

noncomputable def nb076_alpha_dummy_128 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_120))).fv) 1)

noncomputable def nb076_alpha_dummy_129 (g : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_122 g b))).fv) 0)

noncomputable def nb076_alpha_dummy_130 (g : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_122 g b))).fv) 1)

noncomputable def nb076_alpha_dummy_131 : Var := (freshVar (((Wff.classMem (Class.cv (nb076_alpha_dummy_127)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_127)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_127))).fv) 0)

noncomputable def nb076_alpha_dummy_132 (g : Var) (b : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb076_alpha_dummy_129 g b)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_129 g b)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_129 g b))).fv) 0)

noncomputable def nb076_alpha_dummy_133 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb076_alpha_dummy_134 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb076_alpha_dummy_135 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb076_alpha_dummy_136 (g : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb076_alpha_dummy_137 (g : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb076_alpha_dummy_138 (g : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb076_alpha_dummy_139 : Var := (freshVar (((syn_cnin (Class.cv (nb076_alpha_dummy_134)) (Class.cv (nb076_alpha_dummy_135)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_134)) (Class.cv (nb076_alpha_dummy_135)))).fv) 0)

noncomputable def nb076_alpha_dummy_140 (g : Var) (b : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb076_alpha_dummy_137 g b)) (Class.cv (nb076_alpha_dummy_138 g b)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_137 g b)) (Class.cv (nb076_alpha_dummy_138 g b)))).fv) 0)

noncomputable def nb076_alpha_dummy_141 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_134))).fv ∪ ((Class.cv (nb076_alpha_dummy_135))).fv) 0)

noncomputable def nb076_alpha_dummy_142 (g : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_137 g b))).fv ∪ ((Class.cv (nb076_alpha_dummy_138 g b))).fv) 0)

noncomputable def nb076_alpha_dummy_143 : Var := (freshVar (((syn_ccompl (Class.cv (nb076_alpha_dummy_134)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_135)))).fv) 0)

noncomputable def nb076_alpha_dummy_144 (g : Var) (b : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb076_alpha_dummy_137 g b)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_138 g b)))).fv) 0)

noncomputable def nb076_alpha_dummy_145 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_134))).fv ∪ ((Class.cv (nb076_alpha_dummy_134))).fv) 0)

noncomputable def nb076_alpha_dummy_146 (g : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_137 g b))).fv ∪ ((Class.cv (nb076_alpha_dummy_137 g b))).fv) 0)

noncomputable def nb076_alpha_dummy_147 : Var := (freshVar (((Class.cv (nb076_alpha_dummy_135))).fv ∪ ((Class.cv (nb076_alpha_dummy_135))).fv) 0)

noncomputable def nb076_alpha_dummy_148 (g : Var) (b : Var) : Var := (freshVar (((Class.cv (nb076_alpha_dummy_138 g b))).fv ∪ ((Class.cv (nb076_alpha_dummy_138 g b))).fv) 0)

noncomputable def nb076_alpha_dummy_149 : Var := (freshVar (((Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120))) (syn_csn (syn_c0c))))))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
