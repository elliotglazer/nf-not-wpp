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

noncomputable def nominal_df_swap
    (x : Var) (y : Var) (z : Var) (w : Var) (dv_w_x : w ≠ x) (dv_w_y : w ≠ y) (dv_w_z : w ≠ z) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf (.classEq (syn_cswap) (syn_copab x y (syn_wex z (syn_wex w (syn_wa (.classEq (.cv x) (syn_cop (.cv z) (.cv w))) (.classEq (.cv y) (syn_cop (.cv w) (.cv z)))))))) := by
  let alpha_dummy_000 : Var := (freshVar ((∅ : Finset Var)) 0)
  let alpha_dummy_001 : Var := (freshVar ((∅ : Finset Var)) 1)
  let alpha_dummy_002 : Var := (freshVar ((∅ : Finset Var)) 2)
  let alpha_dummy_003 : Var := (freshVar ((∅ : Finset Var)) 3)
  let alpha_dummy_004 : Var := (freshVar (({alpha_dummy_001} : Finset Var) ∪ ({alpha_dummy_002} : Finset Var) ∪ ((syn_wex alpha_dummy_003 (syn_wex alpha_dummy_000 (syn_wa (Wff.classEq (Class.cv alpha_dummy_001) (syn_cop (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_000))) (Wff.classEq (Class.cv alpha_dummy_002) (syn_cop (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_003))))))).fv) 0)
  let alpha_dummy_005 : Var := (freshVar (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ((syn_wex z (syn_wex w (syn_wa (Wff.classEq (Class.cv x) (syn_cop (Class.cv z) (Class.cv w))) (Wff.classEq (Class.cv y) (syn_cop (Class.cv w) (Class.cv z))))))).fv) 0)
  let alpha_dummy_006 : Var := (freshVar (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) 0)
  let alpha_dummy_007 : Var := (freshVar (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) 1)
  let alpha_dummy_008 : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)
  let alpha_dummy_009 : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)
  let alpha_dummy_010 : Var := (freshVar (((syn_ccompl (Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_001) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cphi (Class.cv alpha_dummy_007))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_002) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cun (syn_cphi (Class.cv alpha_dummy_007)) (syn_csn (syn_c0c)))))))).fv) 0)
  let alpha_dummy_011 : Var := (freshVar (((syn_ccompl (Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv x) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cphi (Class.cv alpha_dummy_009))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv y) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cun (syn_cphi (Class.cv alpha_dummy_009)) (syn_csn (syn_c0c)))))))).fv) 0)
  let alpha_dummy_012 : Var := (freshVar (((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_001) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cphi (Class.cv alpha_dummy_007)))))).fv ∪ ((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_001) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cphi (Class.cv alpha_dummy_007)))))).fv) 0)
  let alpha_dummy_013 : Var := (freshVar (((Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv x) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cphi (Class.cv alpha_dummy_009)))))).fv ∪ ((Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv x) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cphi (Class.cv alpha_dummy_009)))))).fv) 0)
  let alpha_dummy_014 : Var := (freshVar (((Class.cv alpha_dummy_007)).fv) 0)
  let alpha_dummy_015 : Var := (freshVar (((Class.cv alpha_dummy_007)).fv) 1)
  let alpha_dummy_016 : Var := (freshVar (((Class.cv alpha_dummy_009)).fv) 0)
  let alpha_dummy_017 : Var := (freshVar (((Class.cv alpha_dummy_009)).fv) 1)
  let alpha_dummy_018 : Var := (freshVar (((Wff.classMem (Class.cv alpha_dummy_014) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv alpha_dummy_014) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_014)).fv) 0)
  let alpha_dummy_019 : Var := (freshVar (((Wff.classMem (Class.cv alpha_dummy_016) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv alpha_dummy_016) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_016)).fv) 0)
  let alpha_dummy_020 : Var := (freshVar (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_021 : Var := (freshVar (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) 1)
  let alpha_dummy_022 : Var := (freshVar (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) 2)
  let alpha_dummy_023 : Var := (freshVar (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_024 : Var := (freshVar (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) 1)
  let alpha_dummy_025 : Var := (freshVar (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) 2)
  let alpha_dummy_026 : Var := (freshVar (((syn_cnin (Class.cv alpha_dummy_021) (Class.cv alpha_dummy_022))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_021) (Class.cv alpha_dummy_022))).fv) 0)
  let alpha_dummy_027 : Var := (freshVar (((syn_cnin (Class.cv alpha_dummy_024) (Class.cv alpha_dummy_025))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_024) (Class.cv alpha_dummy_025))).fv) 0)
  let alpha_dummy_028 : Var := (freshVar (((Class.cv alpha_dummy_021)).fv ∪ ((Class.cv alpha_dummy_022)).fv) 0)
  let alpha_dummy_029 : Var := (freshVar (((Class.cv alpha_dummy_024)).fv ∪ ((Class.cv alpha_dummy_025)).fv) 0)
  let alpha_dummy_030 : Var := (freshVar (((syn_ccompl (Class.cv alpha_dummy_021))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_022))).fv) 0)
  let alpha_dummy_031 : Var := (freshVar (((syn_ccompl (Class.cv alpha_dummy_024))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_025))).fv) 0)
  let alpha_dummy_032 : Var := (freshVar (((Class.cv alpha_dummy_021)).fv ∪ ((Class.cv alpha_dummy_021)).fv) 0)
  let alpha_dummy_033 : Var := (freshVar (((Class.cv alpha_dummy_024)).fv ∪ ((Class.cv alpha_dummy_024)).fv) 0)
  let alpha_dummy_034 : Var := (freshVar (((Class.cv alpha_dummy_022)).fv ∪ ((Class.cv alpha_dummy_022)).fv) 0)
  let alpha_dummy_035 : Var := (freshVar (((Class.cv alpha_dummy_025)).fv ∪ ((Class.cv alpha_dummy_025)).fv) 0)
  let alpha_dummy_036 : Var := (freshVar (((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_002) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cun (syn_cphi (Class.cv alpha_dummy_007)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_002) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cun (syn_cphi (Class.cv alpha_dummy_007)) (syn_csn (syn_c0c))))))).fv) 0)
  let alpha_dummy_037 : Var := (freshVar (((Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv y) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cun (syn_cphi (Class.cv alpha_dummy_009)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv y) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cun (syn_cphi (Class.cv alpha_dummy_009)) (syn_csn (syn_c0c))))))).fv) 0)
  let alpha_dummy_038 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_007)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)
  let alpha_dummy_039 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_009)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)
  let alpha_dummy_040 : Var := (freshVar (((syn_cphi (Class.cv alpha_dummy_007))).fv ∪ ((syn_cphi (Class.cv alpha_dummy_007))).fv) 0)
  let alpha_dummy_041 : Var := (freshVar (((syn_cphi (Class.cv alpha_dummy_009))).fv ∪ ((syn_cphi (Class.cv alpha_dummy_009))).fv) 0)
  let alpha_dummy_042 : Var := (freshVar (((Class.cv alpha_dummy_003)).fv ∪ ((Class.cv alpha_dummy_000)).fv) 0)
  let alpha_dummy_043 : Var := (freshVar (((Class.cv alpha_dummy_003)).fv ∪ ((Class.cv alpha_dummy_000)).fv) 1)
  let alpha_dummy_044 : Var := (freshVar (((Class.cv z)).fv ∪ ((Class.cv w)).fv) 0)
  let alpha_dummy_045 : Var := (freshVar (((Class.cv z)).fv ∪ ((Class.cv w)).fv) 1)
  let alpha_dummy_046 : Var := (freshVar (((syn_ccompl (Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cphi (Class.cv alpha_dummy_043))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c)))))))).fv) 0)
  let alpha_dummy_047 : Var := (freshVar (((syn_ccompl (Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cphi (Class.cv alpha_dummy_045))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cun (syn_cphi (Class.cv alpha_dummy_045)) (syn_csn (syn_c0c)))))))).fv) 0)
  let alpha_dummy_048 : Var := (freshVar (((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cphi (Class.cv alpha_dummy_043)))))).fv ∪ ((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cphi (Class.cv alpha_dummy_043)))))).fv) 0)
  let alpha_dummy_049 : Var := (freshVar (((Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cphi (Class.cv alpha_dummy_045)))))).fv ∪ ((Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cphi (Class.cv alpha_dummy_045)))))).fv) 0)
  let alpha_dummy_050 : Var := (freshVar (((Class.cv alpha_dummy_043)).fv) 0)
  let alpha_dummy_051 : Var := (freshVar (((Class.cv alpha_dummy_043)).fv) 1)
  let alpha_dummy_052 : Var := (freshVar (((Class.cv alpha_dummy_045)).fv) 0)
  let alpha_dummy_053 : Var := (freshVar (((Class.cv alpha_dummy_045)).fv) 1)
  let alpha_dummy_054 : Var := (freshVar (((Wff.classMem (Class.cv alpha_dummy_050) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv alpha_dummy_050) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_050)).fv) 0)
  let alpha_dummy_055 : Var := (freshVar (((Wff.classMem (Class.cv alpha_dummy_052) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv alpha_dummy_052) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_052)).fv) 0)
  let alpha_dummy_056 : Var := (freshVar (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_057 : Var := (freshVar (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) 1)
  let alpha_dummy_058 : Var := (freshVar (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) 2)
  let alpha_dummy_059 : Var := (freshVar (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_060 : Var := (freshVar (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) 1)
  let alpha_dummy_061 : Var := (freshVar (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) 2)
  let alpha_dummy_062 : Var := (freshVar (((syn_cnin (Class.cv alpha_dummy_057) (Class.cv alpha_dummy_058))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_057) (Class.cv alpha_dummy_058))).fv) 0)
  let alpha_dummy_063 : Var := (freshVar (((syn_cnin (Class.cv alpha_dummy_060) (Class.cv alpha_dummy_061))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_060) (Class.cv alpha_dummy_061))).fv) 0)
  let alpha_dummy_064 : Var := (freshVar (((Class.cv alpha_dummy_057)).fv ∪ ((Class.cv alpha_dummy_058)).fv) 0)
  let alpha_dummy_065 : Var := (freshVar (((Class.cv alpha_dummy_060)).fv ∪ ((Class.cv alpha_dummy_061)).fv) 0)
  let alpha_dummy_066 : Var := (freshVar (((syn_ccompl (Class.cv alpha_dummy_057))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_058))).fv) 0)
  let alpha_dummy_067 : Var := (freshVar (((syn_ccompl (Class.cv alpha_dummy_060))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_061))).fv) 0)
  let alpha_dummy_068 : Var := (freshVar (((Class.cv alpha_dummy_057)).fv ∪ ((Class.cv alpha_dummy_057)).fv) 0)
  let alpha_dummy_069 : Var := (freshVar (((Class.cv alpha_dummy_060)).fv ∪ ((Class.cv alpha_dummy_060)).fv) 0)
  let alpha_dummy_070 : Var := (freshVar (((Class.cv alpha_dummy_058)).fv ∪ ((Class.cv alpha_dummy_058)).fv) 0)
  let alpha_dummy_071 : Var := (freshVar (((Class.cv alpha_dummy_061)).fv ∪ ((Class.cv alpha_dummy_061)).fv) 0)
  let alpha_dummy_072 : Var := (freshVar (((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c))))))).fv) 0)
  let alpha_dummy_073 : Var := (freshVar (((Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cun (syn_cphi (Class.cv alpha_dummy_045)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cun (syn_cphi (Class.cv alpha_dummy_045)) (syn_csn (syn_c0c))))))).fv) 0)
  let alpha_dummy_074 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_043)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)
  let alpha_dummy_075 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_045)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)
  let alpha_dummy_076 : Var := (freshVar (((syn_cphi (Class.cv alpha_dummy_043))).fv ∪ ((syn_cphi (Class.cv alpha_dummy_043))).fv) 0)
  let alpha_dummy_077 : Var := (freshVar (((syn_cphi (Class.cv alpha_dummy_045))).fv ∪ ((syn_cphi (Class.cv alpha_dummy_045))).fv) 0)
  let alpha_dummy_078 : Var := (freshVar (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_003)).fv) 0)
  let alpha_dummy_079 : Var := (freshVar (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_003)).fv) 1)
  let alpha_dummy_080 : Var := (freshVar (((Class.cv w)).fv ∪ ((Class.cv z)).fv) 0)
  let alpha_dummy_081 : Var := (freshVar (((Class.cv w)).fv ∪ ((Class.cv z)).fv) 1)
  let alpha_dummy_082 : Var := (freshVar (((syn_ccompl (Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cphi (Class.cv alpha_dummy_079))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cun (syn_cphi (Class.cv alpha_dummy_079)) (syn_csn (syn_c0c)))))))).fv) 0)
  let alpha_dummy_083 : Var := (freshVar (((syn_ccompl (Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cphi (Class.cv alpha_dummy_081))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cun (syn_cphi (Class.cv alpha_dummy_081)) (syn_csn (syn_c0c)))))))).fv) 0)
  let alpha_dummy_084 : Var := (freshVar (((Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cphi (Class.cv alpha_dummy_079)))))).fv ∪ ((Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cphi (Class.cv alpha_dummy_079)))))).fv) 0)
  let alpha_dummy_085 : Var := (freshVar (((Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cphi (Class.cv alpha_dummy_081)))))).fv ∪ ((Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cphi (Class.cv alpha_dummy_081)))))).fv) 0)
  let alpha_dummy_086 : Var := (freshVar (((Class.cv alpha_dummy_079)).fv) 0)
  let alpha_dummy_087 : Var := (freshVar (((Class.cv alpha_dummy_079)).fv) 1)
  let alpha_dummy_088 : Var := (freshVar (((Class.cv alpha_dummy_081)).fv) 0)
  let alpha_dummy_089 : Var := (freshVar (((Class.cv alpha_dummy_081)).fv) 1)
  let alpha_dummy_090 : Var := (freshVar (((Wff.classMem (Class.cv alpha_dummy_086) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv alpha_dummy_086) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_086)).fv) 0)
  let alpha_dummy_091 : Var := (freshVar (((Wff.classMem (Class.cv alpha_dummy_088) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv alpha_dummy_088) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_088)).fv) 0)
  let alpha_dummy_092 : Var := (freshVar (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_093 : Var := (freshVar (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) 1)
  let alpha_dummy_094 : Var := (freshVar (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) 2)
  let alpha_dummy_095 : Var := (freshVar (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_096 : Var := (freshVar (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) 1)
  let alpha_dummy_097 : Var := (freshVar (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) 2)
  let alpha_dummy_098 : Var := (freshVar (((syn_cnin (Class.cv alpha_dummy_093) (Class.cv alpha_dummy_094))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_093) (Class.cv alpha_dummy_094))).fv) 0)
  let alpha_dummy_099 : Var := (freshVar (((syn_cnin (Class.cv alpha_dummy_096) (Class.cv alpha_dummy_097))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_096) (Class.cv alpha_dummy_097))).fv) 0)
  let alpha_dummy_100 : Var := (freshVar (((Class.cv alpha_dummy_093)).fv ∪ ((Class.cv alpha_dummy_094)).fv) 0)
  let alpha_dummy_101 : Var := (freshVar (((Class.cv alpha_dummy_096)).fv ∪ ((Class.cv alpha_dummy_097)).fv) 0)
  let alpha_dummy_102 : Var := (freshVar (((syn_ccompl (Class.cv alpha_dummy_093))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_094))).fv) 0)
  let alpha_dummy_103 : Var := (freshVar (((syn_ccompl (Class.cv alpha_dummy_096))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_097))).fv) 0)
  let alpha_dummy_104 : Var := (freshVar (((Class.cv alpha_dummy_093)).fv ∪ ((Class.cv alpha_dummy_093)).fv) 0)
  let alpha_dummy_105 : Var := (freshVar (((Class.cv alpha_dummy_096)).fv ∪ ((Class.cv alpha_dummy_096)).fv) 0)
  let alpha_dummy_106 : Var := (freshVar (((Class.cv alpha_dummy_094)).fv ∪ ((Class.cv alpha_dummy_094)).fv) 0)
  let alpha_dummy_107 : Var := (freshVar (((Class.cv alpha_dummy_097)).fv ∪ ((Class.cv alpha_dummy_097)).fv) 0)
  let alpha_dummy_108 : Var := (freshVar (((Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cun (syn_cphi (Class.cv alpha_dummy_079)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cun (syn_cphi (Class.cv alpha_dummy_079)) (syn_csn (syn_c0c))))))).fv) 0)
  let alpha_dummy_109 : Var := (freshVar (((Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cun (syn_cphi (Class.cv alpha_dummy_081)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cun (syn_cphi (Class.cv alpha_dummy_081)) (syn_csn (syn_c0c))))))).fv) 0)
  let alpha_dummy_110 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_079)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)
  let alpha_dummy_111 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_081)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)
  let alpha_dummy_112 : Var := (freshVar (((syn_cphi (Class.cv alpha_dummy_079))).fv ∪ ((syn_cphi (Class.cv alpha_dummy_079))).fv) 0)
  let alpha_dummy_113 : Var := (freshVar (((syn_cphi (Class.cv alpha_dummy_081))).fv ∪ ((syn_cphi (Class.cv alpha_dummy_081))).fv) 0)
  have fresh_000 : alpha_dummy_012 ∉ (((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_001) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cphi (Class.cv alpha_dummy_007)))))).fv ∪ ((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_001) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cphi (Class.cv alpha_dummy_007)))))).fv) := by
    simpa [alpha_dummy_012] using freshVar_not_mem (((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_001) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cphi (Class.cv alpha_dummy_007)))))).fv ∪ ((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_001) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cphi (Class.cv alpha_dummy_007)))))).fv) 0
  have fresh_001 : alpha_dummy_036 ∉ (((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_002) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cun (syn_cphi (Class.cv alpha_dummy_007)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_002) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cun (syn_cphi (Class.cv alpha_dummy_007)) (syn_csn (syn_c0c))))))).fv) := by
    simpa [alpha_dummy_036] using freshVar_not_mem (((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_002) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cun (syn_cphi (Class.cv alpha_dummy_007)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_002) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cun (syn_cphi (Class.cv alpha_dummy_007)) (syn_csn (syn_c0c))))))).fv) 0
  have fresh_002 : alpha_dummy_013 ∉ (((Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv x) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cphi (Class.cv alpha_dummy_009)))))).fv ∪ ((Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv x) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cphi (Class.cv alpha_dummy_009)))))).fv) := by
    simpa [alpha_dummy_013] using freshVar_not_mem (((Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv x) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cphi (Class.cv alpha_dummy_009)))))).fv ∪ ((Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv x) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cphi (Class.cv alpha_dummy_009)))))).fv) 0
  have fresh_003 : alpha_dummy_037 ∉ (((Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv y) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cun (syn_cphi (Class.cv alpha_dummy_009)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv y) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cun (syn_cphi (Class.cv alpha_dummy_009)) (syn_csn (syn_c0c))))))).fv) := by
    simpa [alpha_dummy_037] using freshVar_not_mem (((Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv y) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cun (syn_cphi (Class.cv alpha_dummy_009)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv y) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cun (syn_cphi (Class.cv alpha_dummy_009)) (syn_csn (syn_c0c))))))).fv) 0
  have fresh_004 : alpha_dummy_072 ∉ (((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c))))))).fv) := by
    simpa [alpha_dummy_072] using freshVar_not_mem (((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c))))))).fv) 0
  have fresh_005 : alpha_dummy_048 ∉ (((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cphi (Class.cv alpha_dummy_043)))))).fv ∪ ((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cphi (Class.cv alpha_dummy_043)))))).fv) := by
    simpa [alpha_dummy_048] using freshVar_not_mem (((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cphi (Class.cv alpha_dummy_043)))))).fv ∪ ((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cphi (Class.cv alpha_dummy_043)))))).fv) 0
  have fresh_006 : alpha_dummy_073 ∉ (((Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cun (syn_cphi (Class.cv alpha_dummy_045)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cun (syn_cphi (Class.cv alpha_dummy_045)) (syn_csn (syn_c0c))))))).fv) := by
    simpa [alpha_dummy_073] using freshVar_not_mem (((Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cun (syn_cphi (Class.cv alpha_dummy_045)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cun (syn_cphi (Class.cv alpha_dummy_045)) (syn_csn (syn_c0c))))))).fv) 0
  have fresh_007 : alpha_dummy_049 ∉ (((Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cphi (Class.cv alpha_dummy_045)))))).fv ∪ ((Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cphi (Class.cv alpha_dummy_045)))))).fv) := by
    simpa [alpha_dummy_049] using freshVar_not_mem (((Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cphi (Class.cv alpha_dummy_045)))))).fv ∪ ((Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cphi (Class.cv alpha_dummy_045)))))).fv) 0
  have fresh_008 : alpha_dummy_084 ∉ (((Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cphi (Class.cv alpha_dummy_079)))))).fv ∪ ((Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cphi (Class.cv alpha_dummy_079)))))).fv) := by
    simpa [alpha_dummy_084] using freshVar_not_mem (((Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cphi (Class.cv alpha_dummy_079)))))).fv ∪ ((Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cphi (Class.cv alpha_dummy_079)))))).fv) 0
  have fresh_009 : alpha_dummy_108 ∉ (((Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cun (syn_cphi (Class.cv alpha_dummy_079)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cun (syn_cphi (Class.cv alpha_dummy_079)) (syn_csn (syn_c0c))))))).fv) := by
    simpa [alpha_dummy_108] using freshVar_not_mem (((Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cun (syn_cphi (Class.cv alpha_dummy_079)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cun (syn_cphi (Class.cv alpha_dummy_079)) (syn_csn (syn_c0c))))))).fv) 0
  have fresh_010 : alpha_dummy_085 ∉ (((Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cphi (Class.cv alpha_dummy_081)))))).fv ∪ ((Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cphi (Class.cv alpha_dummy_081)))))).fv) := by
    simpa [alpha_dummy_085] using freshVar_not_mem (((Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cphi (Class.cv alpha_dummy_081)))))).fv ∪ ((Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cphi (Class.cv alpha_dummy_081)))))).fv) 0
  have fresh_011 : alpha_dummy_109 ∉ (((Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cun (syn_cphi (Class.cv alpha_dummy_081)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cun (syn_cphi (Class.cv alpha_dummy_081)) (syn_csn (syn_c0c))))))).fv) := by
    simpa [alpha_dummy_109] using freshVar_not_mem (((Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cun (syn_cphi (Class.cv alpha_dummy_081)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cun (syn_cphi (Class.cv alpha_dummy_081)) (syn_csn (syn_c0c))))))).fv) 0
  have fresh_012 : alpha_dummy_078 ∉ (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_003)).fv) := by
    simpa [alpha_dummy_078] using freshVar_not_mem (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_003)).fv) 0
  have fresh_013 : alpha_dummy_079 ∉ (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_003)).fv) := by
    simpa [alpha_dummy_079] using freshVar_not_mem (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_003)).fv) 1
  have distinct_014 : alpha_dummy_078 ≠ alpha_dummy_079 := by
    simpa [alpha_dummy_078, alpha_dummy_079] using
      (freshVar_injective (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_003)).fv) (i := 0) (j := 1) (by decide))
  have fresh_015 : alpha_dummy_006 ∉ (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) := by
    simpa [alpha_dummy_006] using freshVar_not_mem (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) 0
  have fresh_016 : alpha_dummy_007 ∉ (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) := by
    simpa [alpha_dummy_007] using freshVar_not_mem (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) 1
  have distinct_017 : alpha_dummy_006 ≠ alpha_dummy_007 := by
    simpa [alpha_dummy_006, alpha_dummy_007] using
      (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) (i := 0) (j := 1) (by decide))
  have fresh_018 : alpha_dummy_042 ∉ (((Class.cv alpha_dummy_003)).fv ∪ ((Class.cv alpha_dummy_000)).fv) := by
    simpa [alpha_dummy_042] using freshVar_not_mem (((Class.cv alpha_dummy_003)).fv ∪ ((Class.cv alpha_dummy_000)).fv) 0
  have fresh_019 : alpha_dummy_043 ∉ (((Class.cv alpha_dummy_003)).fv ∪ ((Class.cv alpha_dummy_000)).fv) := by
    simpa [alpha_dummy_043] using freshVar_not_mem (((Class.cv alpha_dummy_003)).fv ∪ ((Class.cv alpha_dummy_000)).fv) 1
  have distinct_020 : alpha_dummy_042 ≠ alpha_dummy_043 := by
    simpa [alpha_dummy_042, alpha_dummy_043] using
      (freshVar_injective (((Class.cv alpha_dummy_003)).fv ∪ ((Class.cv alpha_dummy_000)).fv) (i := 0) (j := 1) (by decide))
  have fresh_021 : alpha_dummy_014 ∉ (((Class.cv alpha_dummy_007)).fv) := by
    simpa [alpha_dummy_014] using freshVar_not_mem (((Class.cv alpha_dummy_007)).fv) 0
  have fresh_022 : alpha_dummy_015 ∉ (((Class.cv alpha_dummy_007)).fv) := by
    simpa [alpha_dummy_015] using freshVar_not_mem (((Class.cv alpha_dummy_007)).fv) 1
  have distinct_023 : alpha_dummy_014 ≠ alpha_dummy_015 := by
    simpa [alpha_dummy_014, alpha_dummy_015] using
      (freshVar_injective (((Class.cv alpha_dummy_007)).fv) (i := 0) (j := 1) (by decide))
  have fresh_024 : alpha_dummy_016 ∉ (((Class.cv alpha_dummy_009)).fv) := by
    simpa [alpha_dummy_016] using freshVar_not_mem (((Class.cv alpha_dummy_009)).fv) 0
  have fresh_025 : alpha_dummy_017 ∉ (((Class.cv alpha_dummy_009)).fv) := by
    simpa [alpha_dummy_017] using freshVar_not_mem (((Class.cv alpha_dummy_009)).fv) 1
  have distinct_026 : alpha_dummy_016 ≠ alpha_dummy_017 := by
    simpa [alpha_dummy_016, alpha_dummy_017] using
      (freshVar_injective (((Class.cv alpha_dummy_009)).fv) (i := 0) (j := 1) (by decide))
  have fresh_027 : alpha_dummy_020 ∉ (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) := by
    simpa [alpha_dummy_020] using freshVar_not_mem (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) 0
  have fresh_028 : alpha_dummy_021 ∉ (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) := by
    simpa [alpha_dummy_021] using freshVar_not_mem (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) 1
  have fresh_029 : alpha_dummy_022 ∉ (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) := by
    simpa [alpha_dummy_022] using freshVar_not_mem (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) 2
  have distinct_030 : alpha_dummy_020 ≠ alpha_dummy_021 := by
    simpa [alpha_dummy_020, alpha_dummy_021] using
      (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))
  have distinct_031 : alpha_dummy_020 ≠ alpha_dummy_022 := by
    simpa [alpha_dummy_020, alpha_dummy_022] using
      (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))
  have distinct_032 : alpha_dummy_021 ≠ alpha_dummy_022 := by
    simpa [alpha_dummy_021, alpha_dummy_022] using
      (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))
  have fresh_033 : alpha_dummy_023 ∉ (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) := by
    simpa [alpha_dummy_023] using freshVar_not_mem (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) 0
  have fresh_034 : alpha_dummy_024 ∉ (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) := by
    simpa [alpha_dummy_024] using freshVar_not_mem (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) 1
  have fresh_035 : alpha_dummy_025 ∉ (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) := by
    simpa [alpha_dummy_025] using freshVar_not_mem (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) 2
  have distinct_036 : alpha_dummy_023 ≠ alpha_dummy_024 := by
    simpa [alpha_dummy_023, alpha_dummy_024] using
      (freshVar_injective (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))
  have distinct_037 : alpha_dummy_023 ≠ alpha_dummy_025 := by
    simpa [alpha_dummy_023, alpha_dummy_025] using
      (freshVar_injective (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))
  have distinct_038 : alpha_dummy_024 ≠ alpha_dummy_025 := by
    simpa [alpha_dummy_024, alpha_dummy_025] using
      (freshVar_injective (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))
  have fresh_039 : alpha_dummy_032 ∉ (((Class.cv alpha_dummy_021)).fv ∪ ((Class.cv alpha_dummy_021)).fv) := by
    simpa [alpha_dummy_032] using freshVar_not_mem (((Class.cv alpha_dummy_021)).fv ∪ ((Class.cv alpha_dummy_021)).fv) 0
  have fresh_040 : alpha_dummy_028 ∉ (((Class.cv alpha_dummy_021)).fv ∪ ((Class.cv alpha_dummy_022)).fv) := by
    simpa [alpha_dummy_028] using freshVar_not_mem (((Class.cv alpha_dummy_021)).fv ∪ ((Class.cv alpha_dummy_022)).fv) 0
  have fresh_041 : alpha_dummy_034 ∉ (((Class.cv alpha_dummy_022)).fv ∪ ((Class.cv alpha_dummy_022)).fv) := by
    simpa [alpha_dummy_034] using freshVar_not_mem (((Class.cv alpha_dummy_022)).fv ∪ ((Class.cv alpha_dummy_022)).fv) 0
  have fresh_042 : alpha_dummy_033 ∉ (((Class.cv alpha_dummy_024)).fv ∪ ((Class.cv alpha_dummy_024)).fv) := by
    simpa [alpha_dummy_033] using freshVar_not_mem (((Class.cv alpha_dummy_024)).fv ∪ ((Class.cv alpha_dummy_024)).fv) 0
  have fresh_043 : alpha_dummy_029 ∉ (((Class.cv alpha_dummy_024)).fv ∪ ((Class.cv alpha_dummy_025)).fv) := by
    simpa [alpha_dummy_029] using freshVar_not_mem (((Class.cv alpha_dummy_024)).fv ∪ ((Class.cv alpha_dummy_025)).fv) 0
  have fresh_044 : alpha_dummy_035 ∉ (((Class.cv alpha_dummy_025)).fv ∪ ((Class.cv alpha_dummy_025)).fv) := by
    simpa [alpha_dummy_035] using freshVar_not_mem (((Class.cv alpha_dummy_025)).fv ∪ ((Class.cv alpha_dummy_025)).fv) 0
  have fresh_045 : alpha_dummy_050 ∉ (((Class.cv alpha_dummy_043)).fv) := by
    simpa [alpha_dummy_050] using freshVar_not_mem (((Class.cv alpha_dummy_043)).fv) 0
  have fresh_046 : alpha_dummy_051 ∉ (((Class.cv alpha_dummy_043)).fv) := by
    simpa [alpha_dummy_051] using freshVar_not_mem (((Class.cv alpha_dummy_043)).fv) 1
  have distinct_047 : alpha_dummy_050 ≠ alpha_dummy_051 := by
    simpa [alpha_dummy_050, alpha_dummy_051] using
      (freshVar_injective (((Class.cv alpha_dummy_043)).fv) (i := 0) (j := 1) (by decide))
  have fresh_048 : alpha_dummy_052 ∉ (((Class.cv alpha_dummy_045)).fv) := by
    simpa [alpha_dummy_052] using freshVar_not_mem (((Class.cv alpha_dummy_045)).fv) 0
  have fresh_049 : alpha_dummy_053 ∉ (((Class.cv alpha_dummy_045)).fv) := by
    simpa [alpha_dummy_053] using freshVar_not_mem (((Class.cv alpha_dummy_045)).fv) 1
  have distinct_050 : alpha_dummy_052 ≠ alpha_dummy_053 := by
    simpa [alpha_dummy_052, alpha_dummy_053] using
      (freshVar_injective (((Class.cv alpha_dummy_045)).fv) (i := 0) (j := 1) (by decide))
  have fresh_051 : alpha_dummy_056 ∉ (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) := by
    simpa [alpha_dummy_056] using freshVar_not_mem (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) 0
  have fresh_052 : alpha_dummy_057 ∉ (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) := by
    simpa [alpha_dummy_057] using freshVar_not_mem (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) 1
  have fresh_053 : alpha_dummy_058 ∉ (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) := by
    simpa [alpha_dummy_058] using freshVar_not_mem (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) 2
  have distinct_054 : alpha_dummy_056 ≠ alpha_dummy_057 := by
    simpa [alpha_dummy_056, alpha_dummy_057] using
      (freshVar_injective (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))
  have distinct_055 : alpha_dummy_056 ≠ alpha_dummy_058 := by
    simpa [alpha_dummy_056, alpha_dummy_058] using
      (freshVar_injective (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))
  have distinct_056 : alpha_dummy_057 ≠ alpha_dummy_058 := by
    simpa [alpha_dummy_057, alpha_dummy_058] using
      (freshVar_injective (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))
  have fresh_057 : alpha_dummy_059 ∉ (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) := by
    simpa [alpha_dummy_059] using freshVar_not_mem (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) 0
  have fresh_058 : alpha_dummy_060 ∉ (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) := by
    simpa [alpha_dummy_060] using freshVar_not_mem (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) 1
  have fresh_059 : alpha_dummy_061 ∉ (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) := by
    simpa [alpha_dummy_061] using freshVar_not_mem (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) 2
  have distinct_060 : alpha_dummy_059 ≠ alpha_dummy_060 := by
    simpa [alpha_dummy_059, alpha_dummy_060] using
      (freshVar_injective (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))
  have distinct_061 : alpha_dummy_059 ≠ alpha_dummy_061 := by
    simpa [alpha_dummy_059, alpha_dummy_061] using
      (freshVar_injective (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))
  have distinct_062 : alpha_dummy_060 ≠ alpha_dummy_061 := by
    simpa [alpha_dummy_060, alpha_dummy_061] using
      (freshVar_injective (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))
  have fresh_063 : alpha_dummy_068 ∉ (((Class.cv alpha_dummy_057)).fv ∪ ((Class.cv alpha_dummy_057)).fv) := by
    simpa [alpha_dummy_068] using freshVar_not_mem (((Class.cv alpha_dummy_057)).fv ∪ ((Class.cv alpha_dummy_057)).fv) 0
  have fresh_064 : alpha_dummy_064 ∉ (((Class.cv alpha_dummy_057)).fv ∪ ((Class.cv alpha_dummy_058)).fv) := by
    simpa [alpha_dummy_064] using freshVar_not_mem (((Class.cv alpha_dummy_057)).fv ∪ ((Class.cv alpha_dummy_058)).fv) 0
  have fresh_065 : alpha_dummy_070 ∉ (((Class.cv alpha_dummy_058)).fv ∪ ((Class.cv alpha_dummy_058)).fv) := by
    simpa [alpha_dummy_070] using freshVar_not_mem (((Class.cv alpha_dummy_058)).fv ∪ ((Class.cv alpha_dummy_058)).fv) 0
  have fresh_066 : alpha_dummy_069 ∉ (((Class.cv alpha_dummy_060)).fv ∪ ((Class.cv alpha_dummy_060)).fv) := by
    simpa [alpha_dummy_069] using freshVar_not_mem (((Class.cv alpha_dummy_060)).fv ∪ ((Class.cv alpha_dummy_060)).fv) 0
  have fresh_067 : alpha_dummy_065 ∉ (((Class.cv alpha_dummy_060)).fv ∪ ((Class.cv alpha_dummy_061)).fv) := by
    simpa [alpha_dummy_065] using freshVar_not_mem (((Class.cv alpha_dummy_060)).fv ∪ ((Class.cv alpha_dummy_061)).fv) 0
  have fresh_068 : alpha_dummy_071 ∉ (((Class.cv alpha_dummy_061)).fv ∪ ((Class.cv alpha_dummy_061)).fv) := by
    simpa [alpha_dummy_071] using freshVar_not_mem (((Class.cv alpha_dummy_061)).fv ∪ ((Class.cv alpha_dummy_061)).fv) 0
  have fresh_069 : alpha_dummy_086 ∉ (((Class.cv alpha_dummy_079)).fv) := by
    simpa [alpha_dummy_086] using freshVar_not_mem (((Class.cv alpha_dummy_079)).fv) 0
  have fresh_070 : alpha_dummy_087 ∉ (((Class.cv alpha_dummy_079)).fv) := by
    simpa [alpha_dummy_087] using freshVar_not_mem (((Class.cv alpha_dummy_079)).fv) 1
  have distinct_071 : alpha_dummy_086 ≠ alpha_dummy_087 := by
    simpa [alpha_dummy_086, alpha_dummy_087] using
      (freshVar_injective (((Class.cv alpha_dummy_079)).fv) (i := 0) (j := 1) (by decide))
  have fresh_072 : alpha_dummy_088 ∉ (((Class.cv alpha_dummy_081)).fv) := by
    simpa [alpha_dummy_088] using freshVar_not_mem (((Class.cv alpha_dummy_081)).fv) 0
  have fresh_073 : alpha_dummy_089 ∉ (((Class.cv alpha_dummy_081)).fv) := by
    simpa [alpha_dummy_089] using freshVar_not_mem (((Class.cv alpha_dummy_081)).fv) 1
  have distinct_074 : alpha_dummy_088 ≠ alpha_dummy_089 := by
    simpa [alpha_dummy_088, alpha_dummy_089] using
      (freshVar_injective (((Class.cv alpha_dummy_081)).fv) (i := 0) (j := 1) (by decide))
  have fresh_075 : alpha_dummy_092 ∉ (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) := by
    simpa [alpha_dummy_092] using freshVar_not_mem (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) 0
  have fresh_076 : alpha_dummy_093 ∉ (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) := by
    simpa [alpha_dummy_093] using freshVar_not_mem (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) 1
  have fresh_077 : alpha_dummy_094 ∉ (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) := by
    simpa [alpha_dummy_094] using freshVar_not_mem (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) 2
  have distinct_078 : alpha_dummy_092 ≠ alpha_dummy_093 := by
    simpa [alpha_dummy_092, alpha_dummy_093] using
      (freshVar_injective (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))
  have distinct_079 : alpha_dummy_092 ≠ alpha_dummy_094 := by
    simpa [alpha_dummy_092, alpha_dummy_094] using
      (freshVar_injective (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))
  have distinct_080 : alpha_dummy_093 ≠ alpha_dummy_094 := by
    simpa [alpha_dummy_093, alpha_dummy_094] using
      (freshVar_injective (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))
  have fresh_081 : alpha_dummy_095 ∉ (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) := by
    simpa [alpha_dummy_095] using freshVar_not_mem (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) 0
  have fresh_082 : alpha_dummy_096 ∉ (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) := by
    simpa [alpha_dummy_096] using freshVar_not_mem (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) 1
  have fresh_083 : alpha_dummy_097 ∉ (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) := by
    simpa [alpha_dummy_097] using freshVar_not_mem (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) 2
  have distinct_084 : alpha_dummy_095 ≠ alpha_dummy_096 := by
    simpa [alpha_dummy_095, alpha_dummy_096] using
      (freshVar_injective (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))
  have distinct_085 : alpha_dummy_095 ≠ alpha_dummy_097 := by
    simpa [alpha_dummy_095, alpha_dummy_097] using
      (freshVar_injective (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))
  have distinct_086 : alpha_dummy_096 ≠ alpha_dummy_097 := by
    simpa [alpha_dummy_096, alpha_dummy_097] using
      (freshVar_injective (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))
  have fresh_087 : alpha_dummy_104 ∉ (((Class.cv alpha_dummy_093)).fv ∪ ((Class.cv alpha_dummy_093)).fv) := by
    simpa [alpha_dummy_104] using freshVar_not_mem (((Class.cv alpha_dummy_093)).fv ∪ ((Class.cv alpha_dummy_093)).fv) 0
  have fresh_088 : alpha_dummy_100 ∉ (((Class.cv alpha_dummy_093)).fv ∪ ((Class.cv alpha_dummy_094)).fv) := by
    simpa [alpha_dummy_100] using freshVar_not_mem (((Class.cv alpha_dummy_093)).fv ∪ ((Class.cv alpha_dummy_094)).fv) 0
  have fresh_089 : alpha_dummy_106 ∉ (((Class.cv alpha_dummy_094)).fv ∪ ((Class.cv alpha_dummy_094)).fv) := by
    simpa [alpha_dummy_106] using freshVar_not_mem (((Class.cv alpha_dummy_094)).fv ∪ ((Class.cv alpha_dummy_094)).fv) 0
  have fresh_090 : alpha_dummy_105 ∉ (((Class.cv alpha_dummy_096)).fv ∪ ((Class.cv alpha_dummy_096)).fv) := by
    simpa [alpha_dummy_105] using freshVar_not_mem (((Class.cv alpha_dummy_096)).fv ∪ ((Class.cv alpha_dummy_096)).fv) 0
  have fresh_091 : alpha_dummy_101 ∉ (((Class.cv alpha_dummy_096)).fv ∪ ((Class.cv alpha_dummy_097)).fv) := by
    simpa [alpha_dummy_101] using freshVar_not_mem (((Class.cv alpha_dummy_096)).fv ∪ ((Class.cv alpha_dummy_097)).fv) 0
  have fresh_092 : alpha_dummy_107 ∉ (((Class.cv alpha_dummy_097)).fv ∪ ((Class.cv alpha_dummy_097)).fv) := by
    simpa [alpha_dummy_107] using freshVar_not_mem (((Class.cv alpha_dummy_097)).fv ∪ ((Class.cv alpha_dummy_097)).fv) 0
  have fresh_093 : alpha_dummy_080 ∉ (((Class.cv w)).fv ∪ ((Class.cv z)).fv) := by
    simpa [alpha_dummy_080] using freshVar_not_mem (((Class.cv w)).fv ∪ ((Class.cv z)).fv) 0
  have fresh_094 : alpha_dummy_081 ∉ (((Class.cv w)).fv ∪ ((Class.cv z)).fv) := by
    simpa [alpha_dummy_081] using freshVar_not_mem (((Class.cv w)).fv ∪ ((Class.cv z)).fv) 1
  have distinct_095 : alpha_dummy_080 ≠ alpha_dummy_081 := by
    simpa [alpha_dummy_080, alpha_dummy_081] using
      (freshVar_injective (((Class.cv w)).fv ∪ ((Class.cv z)).fv) (i := 0) (j := 1) (by decide))
  have fresh_096 : alpha_dummy_008 ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
    simpa [alpha_dummy_008] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0
  have fresh_097 : alpha_dummy_009 ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
    simpa [alpha_dummy_009] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1
  have distinct_098 : alpha_dummy_008 ≠ alpha_dummy_009 := by
    simpa [alpha_dummy_008, alpha_dummy_009] using
      (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))
  have fresh_099 : alpha_dummy_044 ∉ (((Class.cv z)).fv ∪ ((Class.cv w)).fv) := by
    simpa [alpha_dummy_044] using freshVar_not_mem (((Class.cv z)).fv ∪ ((Class.cv w)).fv) 0
  have fresh_100 : alpha_dummy_045 ∉ (((Class.cv z)).fv ∪ ((Class.cv w)).fv) := by
    simpa [alpha_dummy_045] using freshVar_not_mem (((Class.cv z)).fv ∪ ((Class.cv w)).fv) 1
  have distinct_101 : alpha_dummy_044 ≠ alpha_dummy_045 := by
    simpa [alpha_dummy_044, alpha_dummy_045] using
      (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv w)).fv) (i := 0) (j := 1) (by decide))
  have fresh_102 : alpha_dummy_018 ∉ (((Wff.classMem (Class.cv alpha_dummy_014) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv alpha_dummy_014) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_014)).fv) := by
    simpa [alpha_dummy_018] using freshVar_not_mem (((Wff.classMem (Class.cv alpha_dummy_014) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv alpha_dummy_014) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_014)).fv) 0
  have fresh_103 : alpha_dummy_019 ∉ (((Wff.classMem (Class.cv alpha_dummy_016) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv alpha_dummy_016) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_016)).fv) := by
    simpa [alpha_dummy_019] using freshVar_not_mem (((Wff.classMem (Class.cv alpha_dummy_016) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv alpha_dummy_016) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_016)).fv) 0
  have fresh_104 : alpha_dummy_054 ∉ (((Wff.classMem (Class.cv alpha_dummy_050) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv alpha_dummy_050) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_050)).fv) := by
    simpa [alpha_dummy_054] using freshVar_not_mem (((Wff.classMem (Class.cv alpha_dummy_050) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv alpha_dummy_050) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_050)).fv) 0
  have fresh_105 : alpha_dummy_055 ∉ (((Wff.classMem (Class.cv alpha_dummy_052) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv alpha_dummy_052) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_052)).fv) := by
    simpa [alpha_dummy_055] using freshVar_not_mem (((Wff.classMem (Class.cv alpha_dummy_052) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv alpha_dummy_052) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_052)).fv) 0
  have fresh_106 : alpha_dummy_090 ∉ (((Wff.classMem (Class.cv alpha_dummy_086) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv alpha_dummy_086) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_086)).fv) := by
    simpa [alpha_dummy_090] using freshVar_not_mem (((Wff.classMem (Class.cv alpha_dummy_086) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv alpha_dummy_086) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_086)).fv) 0
  have fresh_107 : alpha_dummy_091 ∉ (((Wff.classMem (Class.cv alpha_dummy_088) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv alpha_dummy_088) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_088)).fv) := by
    simpa [alpha_dummy_091] using freshVar_not_mem (((Wff.classMem (Class.cv alpha_dummy_088) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv alpha_dummy_088) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_088)).fv) 0
  have fresh_108 : alpha_dummy_010 ∉ (((syn_ccompl (Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_001) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cphi (Class.cv alpha_dummy_007))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_002) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cun (syn_cphi (Class.cv alpha_dummy_007)) (syn_csn (syn_c0c)))))))).fv) := by
    simpa [alpha_dummy_010] using freshVar_not_mem (((syn_ccompl (Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_001) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cphi (Class.cv alpha_dummy_007))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_002) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cun (syn_cphi (Class.cv alpha_dummy_007)) (syn_csn (syn_c0c)))))))).fv) 0
  have fresh_109 : alpha_dummy_011 ∉ (((syn_ccompl (Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv x) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cphi (Class.cv alpha_dummy_009))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv y) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cun (syn_cphi (Class.cv alpha_dummy_009)) (syn_csn (syn_c0c)))))))).fv) := by
    simpa [alpha_dummy_011] using freshVar_not_mem (((syn_ccompl (Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv x) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cphi (Class.cv alpha_dummy_009))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv y) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cun (syn_cphi (Class.cv alpha_dummy_009)) (syn_csn (syn_c0c)))))))).fv) 0
  have fresh_110 : alpha_dummy_046 ∉ (((syn_ccompl (Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cphi (Class.cv alpha_dummy_043))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c)))))))).fv) := by
    simpa [alpha_dummy_046] using freshVar_not_mem (((syn_ccompl (Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cphi (Class.cv alpha_dummy_043))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c)))))))).fv) 0
  have fresh_111 : alpha_dummy_047 ∉ (((syn_ccompl (Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cphi (Class.cv alpha_dummy_045))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cun (syn_cphi (Class.cv alpha_dummy_045)) (syn_csn (syn_c0c)))))))).fv) := by
    simpa [alpha_dummy_047] using freshVar_not_mem (((syn_ccompl (Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cphi (Class.cv alpha_dummy_045))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cun (syn_cphi (Class.cv alpha_dummy_045)) (syn_csn (syn_c0c)))))))).fv) 0
  have fresh_112 : alpha_dummy_082 ∉ (((syn_ccompl (Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cphi (Class.cv alpha_dummy_079))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cun (syn_cphi (Class.cv alpha_dummy_079)) (syn_csn (syn_c0c)))))))).fv) := by
    simpa [alpha_dummy_082] using freshVar_not_mem (((syn_ccompl (Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cphi (Class.cv alpha_dummy_079))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cun (syn_cphi (Class.cv alpha_dummy_079)) (syn_csn (syn_c0c)))))))).fv) 0
  have fresh_113 : alpha_dummy_083 ∉ (((syn_ccompl (Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cphi (Class.cv alpha_dummy_081))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cun (syn_cphi (Class.cv alpha_dummy_081)) (syn_csn (syn_c0c)))))))).fv) := by
    simpa [alpha_dummy_083] using freshVar_not_mem (((syn_ccompl (Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cphi (Class.cv alpha_dummy_081))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cun (syn_cphi (Class.cv alpha_dummy_081)) (syn_csn (syn_c0c)))))))).fv) 0
  have fresh_114 : alpha_dummy_030 ∉ (((syn_ccompl (Class.cv alpha_dummy_021))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_022))).fv) := by
    simpa [alpha_dummy_030] using freshVar_not_mem (((syn_ccompl (Class.cv alpha_dummy_021))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_022))).fv) 0
  have fresh_115 : alpha_dummy_031 ∉ (((syn_ccompl (Class.cv alpha_dummy_024))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_025))).fv) := by
    simpa [alpha_dummy_031] using freshVar_not_mem (((syn_ccompl (Class.cv alpha_dummy_024))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_025))).fv) 0
  have fresh_116 : alpha_dummy_066 ∉ (((syn_ccompl (Class.cv alpha_dummy_057))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_058))).fv) := by
    simpa [alpha_dummy_066] using freshVar_not_mem (((syn_ccompl (Class.cv alpha_dummy_057))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_058))).fv) 0
  have fresh_117 : alpha_dummy_067 ∉ (((syn_ccompl (Class.cv alpha_dummy_060))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_061))).fv) := by
    simpa [alpha_dummy_067] using freshVar_not_mem (((syn_ccompl (Class.cv alpha_dummy_060))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_061))).fv) 0
  have fresh_118 : alpha_dummy_102 ∉ (((syn_ccompl (Class.cv alpha_dummy_093))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_094))).fv) := by
    simpa [alpha_dummy_102] using freshVar_not_mem (((syn_ccompl (Class.cv alpha_dummy_093))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_094))).fv) 0
  have fresh_119 : alpha_dummy_103 ∉ (((syn_ccompl (Class.cv alpha_dummy_096))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_097))).fv) := by
    simpa [alpha_dummy_103] using freshVar_not_mem (((syn_ccompl (Class.cv alpha_dummy_096))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_097))).fv) 0
  have fresh_120 : alpha_dummy_038 ∉ (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_007)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
    simpa [alpha_dummy_038] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_007)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0
  have fresh_121 : alpha_dummy_039 ∉ (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_009)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
    simpa [alpha_dummy_039] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_009)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0
  have fresh_122 : alpha_dummy_074 ∉ (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_043)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
    simpa [alpha_dummy_074] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_043)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0
  have fresh_123 : alpha_dummy_075 ∉ (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_045)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
    simpa [alpha_dummy_075] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_045)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0
  have fresh_124 : alpha_dummy_110 ∉ (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_079)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
    simpa [alpha_dummy_110] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_079)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0
  have fresh_125 : alpha_dummy_111 ∉ (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_081)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
    simpa [alpha_dummy_111] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_081)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0
  have fresh_126 : alpha_dummy_026 ∉ (((syn_cnin (Class.cv alpha_dummy_021) (Class.cv alpha_dummy_022))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_021) (Class.cv alpha_dummy_022))).fv) := by
    simpa [alpha_dummy_026] using freshVar_not_mem (((syn_cnin (Class.cv alpha_dummy_021) (Class.cv alpha_dummy_022))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_021) (Class.cv alpha_dummy_022))).fv) 0
  have fresh_127 : alpha_dummy_027 ∉ (((syn_cnin (Class.cv alpha_dummy_024) (Class.cv alpha_dummy_025))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_024) (Class.cv alpha_dummy_025))).fv) := by
    simpa [alpha_dummy_027] using freshVar_not_mem (((syn_cnin (Class.cv alpha_dummy_024) (Class.cv alpha_dummy_025))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_024) (Class.cv alpha_dummy_025))).fv) 0
  have fresh_128 : alpha_dummy_062 ∉ (((syn_cnin (Class.cv alpha_dummy_057) (Class.cv alpha_dummy_058))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_057) (Class.cv alpha_dummy_058))).fv) := by
    simpa [alpha_dummy_062] using freshVar_not_mem (((syn_cnin (Class.cv alpha_dummy_057) (Class.cv alpha_dummy_058))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_057) (Class.cv alpha_dummy_058))).fv) 0
  have fresh_129 : alpha_dummy_063 ∉ (((syn_cnin (Class.cv alpha_dummy_060) (Class.cv alpha_dummy_061))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_060) (Class.cv alpha_dummy_061))).fv) := by
    simpa [alpha_dummy_063] using freshVar_not_mem (((syn_cnin (Class.cv alpha_dummy_060) (Class.cv alpha_dummy_061))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_060) (Class.cv alpha_dummy_061))).fv) 0
  have fresh_130 : alpha_dummy_098 ∉ (((syn_cnin (Class.cv alpha_dummy_093) (Class.cv alpha_dummy_094))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_093) (Class.cv alpha_dummy_094))).fv) := by
    simpa [alpha_dummy_098] using freshVar_not_mem (((syn_cnin (Class.cv alpha_dummy_093) (Class.cv alpha_dummy_094))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_093) (Class.cv alpha_dummy_094))).fv) 0
  have fresh_131 : alpha_dummy_099 ∉ (((syn_cnin (Class.cv alpha_dummy_096) (Class.cv alpha_dummy_097))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_096) (Class.cv alpha_dummy_097))).fv) := by
    simpa [alpha_dummy_099] using freshVar_not_mem (((syn_cnin (Class.cv alpha_dummy_096) (Class.cv alpha_dummy_097))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_096) (Class.cv alpha_dummy_097))).fv) 0
  have fresh_132 : alpha_dummy_040 ∉ (((syn_cphi (Class.cv alpha_dummy_007))).fv ∪ ((syn_cphi (Class.cv alpha_dummy_007))).fv) := by
    simpa [alpha_dummy_040] using freshVar_not_mem (((syn_cphi (Class.cv alpha_dummy_007))).fv ∪ ((syn_cphi (Class.cv alpha_dummy_007))).fv) 0
  have fresh_133 : alpha_dummy_041 ∉ (((syn_cphi (Class.cv alpha_dummy_009))).fv ∪ ((syn_cphi (Class.cv alpha_dummy_009))).fv) := by
    simpa [alpha_dummy_041] using freshVar_not_mem (((syn_cphi (Class.cv alpha_dummy_009))).fv ∪ ((syn_cphi (Class.cv alpha_dummy_009))).fv) 0
  have fresh_134 : alpha_dummy_076 ∉ (((syn_cphi (Class.cv alpha_dummy_043))).fv ∪ ((syn_cphi (Class.cv alpha_dummy_043))).fv) := by
    simpa [alpha_dummy_076] using freshVar_not_mem (((syn_cphi (Class.cv alpha_dummy_043))).fv ∪ ((syn_cphi (Class.cv alpha_dummy_043))).fv) 0
  have fresh_135 : alpha_dummy_077 ∉ (((syn_cphi (Class.cv alpha_dummy_045))).fv ∪ ((syn_cphi (Class.cv alpha_dummy_045))).fv) := by
    simpa [alpha_dummy_077] using freshVar_not_mem (((syn_cphi (Class.cv alpha_dummy_045))).fv ∪ ((syn_cphi (Class.cv alpha_dummy_045))).fv) 0
  have fresh_136 : alpha_dummy_112 ∉ (((syn_cphi (Class.cv alpha_dummy_079))).fv ∪ ((syn_cphi (Class.cv alpha_dummy_079))).fv) := by
    simpa [alpha_dummy_112] using freshVar_not_mem (((syn_cphi (Class.cv alpha_dummy_079))).fv ∪ ((syn_cphi (Class.cv alpha_dummy_079))).fv) 0
  have fresh_137 : alpha_dummy_113 ∉ (((syn_cphi (Class.cv alpha_dummy_081))).fv ∪ ((syn_cphi (Class.cv alpha_dummy_081))).fv) := by
    simpa [alpha_dummy_113] using freshVar_not_mem (((syn_cphi (Class.cv alpha_dummy_081))).fv ∪ ((syn_cphi (Class.cv alpha_dummy_081))).fv) 0
  have fresh_138 : alpha_dummy_004 ∉ (({alpha_dummy_001} : Finset Var) ∪ ({alpha_dummy_002} : Finset Var) ∪ ((syn_wex alpha_dummy_003 (syn_wex alpha_dummy_000 (syn_wa (Wff.classEq (Class.cv alpha_dummy_001) (syn_cop (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_000))) (Wff.classEq (Class.cv alpha_dummy_002) (syn_cop (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_003))))))).fv) := by
    simpa [alpha_dummy_004] using freshVar_not_mem (({alpha_dummy_001} : Finset Var) ∪ ({alpha_dummy_002} : Finset Var) ∪ ((syn_wex alpha_dummy_003 (syn_wex alpha_dummy_000 (syn_wa (Wff.classEq (Class.cv alpha_dummy_001) (syn_cop (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_000))) (Wff.classEq (Class.cv alpha_dummy_002) (syn_cop (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_003))))))).fv) 0
  have fresh_139 : alpha_dummy_005 ∉ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ((syn_wex z (syn_wex w (syn_wa (Wff.classEq (Class.cv x) (syn_cop (Class.cv z) (Class.cv w))) (Wff.classEq (Class.cv y) (syn_cop (Class.cv w) (Class.cv z))))))).fv) := by
    simpa [alpha_dummy_005] using freshVar_not_mem (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ((syn_wex z (syn_wex w (syn_wa (Wff.classEq (Class.cv x) (syn_cop (Class.cv z) (Class.cv w))) (Wff.classEq (Class.cv y) (syn_cop (Class.cv w) (Class.cv z))))))).fv) 0
  have fresh_140 : alpha_dummy_000 ∉ ((∅ : Finset Var)) := by
    simpa [alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_141 : alpha_dummy_001 ∉ ((∅ : Finset Var)) := by
    simpa [alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1
  have fresh_142 : alpha_dummy_002 ∉ ((∅ : Finset Var)) := by
    simpa [alpha_dummy_002] using freshVar_not_mem ((∅ : Finset Var)) 2
  have fresh_143 : alpha_dummy_003 ∉ ((∅ : Finset Var)) := by
    simpa [alpha_dummy_003] using freshVar_not_mem ((∅ : Finset Var)) 3
  have distinct_144 : alpha_dummy_000 ≠ alpha_dummy_001 := by
    simpa [alpha_dummy_000, alpha_dummy_001] using
      (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))
  have distinct_145 : alpha_dummy_000 ≠ alpha_dummy_002 := by
    simpa [alpha_dummy_000, alpha_dummy_002] using
      (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))
  have distinct_146 : alpha_dummy_000 ≠ alpha_dummy_003 := by
    simpa [alpha_dummy_000, alpha_dummy_003] using
      (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 3) (by decide))
  have distinct_147 : alpha_dummy_001 ≠ alpha_dummy_002 := by
    simpa [alpha_dummy_001, alpha_dummy_002] using
      (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))
  have distinct_148 : alpha_dummy_001 ≠ alpha_dummy_003 := by
    simpa [alpha_dummy_001, alpha_dummy_003] using
      (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 3) (by decide))
  have distinct_149 : alpha_dummy_002 ≠ alpha_dummy_003 := by
    simpa [alpha_dummy_002, alpha_dummy_003] using
      (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 3) (by decide))
  have support_mem_0000 : alpha_dummy_001 ∈ (({alpha_dummy_001} : Finset Var) ∪ ({alpha_dummy_002} : Finset Var) ∪ ((syn_wex alpha_dummy_003 (syn_wex alpha_dummy_000 (syn_wa (Wff.classEq (Class.cv alpha_dummy_001) (syn_cop (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_000))) (Wff.classEq (Class.cv alpha_dummy_002) (syn_cop (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_003))))))).fv) := by
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_singleton_self _
  have support_mem_0001 : x ∈ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ((syn_wex z (syn_wex w (syn_wa (Wff.classEq (Class.cv x) (syn_cop (Class.cv z) (Class.cv w))) (Wff.classEq (Class.cv y) (syn_cop (Class.cv w) (Class.cv z))))))).fv) := by
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_singleton_self _
  have support_mem_0002 : alpha_dummy_002 ∈ (({alpha_dummy_001} : Finset Var) ∪ ({alpha_dummy_002} : Finset Var) ∪ ((syn_wex alpha_dummy_003 (syn_wex alpha_dummy_000 (syn_wa (Wff.classEq (Class.cv alpha_dummy_001) (syn_cop (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_000))) (Wff.classEq (Class.cv alpha_dummy_002) (syn_cop (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_003))))))).fv) := by
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_singleton_self _
  have support_mem_0003 : y ∈ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ((syn_wex z (syn_wex w (syn_wa (Wff.classEq (Class.cv x) (syn_cop (Class.cv z) (Class.cv w))) (Wff.classEq (Class.cv y) (syn_cop (Class.cv w) (Class.cv z))))))).fv) := by
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_singleton_self _
  have support_mem_0004 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0005 : alpha_dummy_001 ∈ (((syn_ccompl (Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_001) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cphi (Class.cv alpha_dummy_007))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_002) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cun (syn_cphi (Class.cv alpha_dummy_007)) (syn_csn (syn_c0c)))))))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
    ·
      rw [fv_syn_wrex]
      apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 1))
      ·
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0006 : x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0007 : x ∈ (((syn_ccompl (Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv x) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cphi (Class.cv alpha_dummy_009))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv y) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cun (syn_cphi (Class.cv alpha_dummy_009)) (syn_csn (syn_c0c)))))))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
    ·
      rw [fv_syn_wrex]
      apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 1))
      ·
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0008 : alpha_dummy_001 ∈ (((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_001) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cphi (Class.cv alpha_dummy_007)))))).fv ∪ ((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_001) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cphi (Class.cv alpha_dummy_007)))))).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
    ·
      rw [fv_syn_wrex]
      apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 1))
      ·
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0009 : x ∈ (((Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv x) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cphi (Class.cv alpha_dummy_009)))))).fv ∪ ((Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv x) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cphi (Class.cv alpha_dummy_009)))))).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
    ·
      rw [fv_syn_wrex]
      apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 1))
      ·
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0010 : alpha_dummy_007 ∈ (((Class.cv alpha_dummy_007)).fv) := by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0011 : alpha_dummy_009 ∈ (((Class.cv alpha_dummy_009)).fv) := by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0012 : alpha_dummy_014 ∈ (((Wff.classMem (Class.cv alpha_dummy_014) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv alpha_dummy_014) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_014)).fv) := by
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    rw [fv_wff_classMem]
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0013 : alpha_dummy_016 ∈ (((Wff.classMem (Class.cv alpha_dummy_016) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv alpha_dummy_016) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_016)).fv) := by
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    rw [fv_wff_classMem]
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0014 : alpha_dummy_014 ∈ (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0015 : alpha_dummy_016 ∈ (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0016 : alpha_dummy_021 ∈ (((syn_cnin (Class.cv alpha_dummy_021) (Class.cv alpha_dummy_022))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_021) (Class.cv alpha_dummy_022))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_cnin]
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0017 : alpha_dummy_024 ∈ (((syn_cnin (Class.cv alpha_dummy_024) (Class.cv alpha_dummy_025))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_024) (Class.cv alpha_dummy_025))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_cnin]
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0018 : alpha_dummy_021 ∈ (((Class.cv alpha_dummy_021)).fv ∪ ((Class.cv alpha_dummy_022)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0019 : alpha_dummy_024 ∈ (((Class.cv alpha_dummy_024)).fv ∪ ((Class.cv alpha_dummy_025)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0020 : alpha_dummy_022 ∈ (((syn_cnin (Class.cv alpha_dummy_021) (Class.cv alpha_dummy_022))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_021) (Class.cv alpha_dummy_022))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_cnin]
    apply Finset.mem_union_right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0021 : alpha_dummy_025 ∈ (((syn_cnin (Class.cv alpha_dummy_024) (Class.cv alpha_dummy_025))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_024) (Class.cv alpha_dummy_025))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_cnin]
    apply Finset.mem_union_right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0022 : alpha_dummy_022 ∈ (((Class.cv alpha_dummy_021)).fv ∪ ((Class.cv alpha_dummy_022)).fv) := by
    apply Finset.mem_union_right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0023 : alpha_dummy_025 ∈ (((Class.cv alpha_dummy_024)).fv ∪ ((Class.cv alpha_dummy_025)).fv) := by
    apply Finset.mem_union_right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0024 : alpha_dummy_021 ∈ (((syn_ccompl (Class.cv alpha_dummy_021))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_022))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0025 : alpha_dummy_024 ∈ (((syn_ccompl (Class.cv alpha_dummy_024))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_025))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0026 : alpha_dummy_021 ∈ (((Class.cv alpha_dummy_021)).fv ∪ ((Class.cv alpha_dummy_021)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0027 : alpha_dummy_024 ∈ (((Class.cv alpha_dummy_024)).fv ∪ ((Class.cv alpha_dummy_024)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0028 : alpha_dummy_022 ∈ (((syn_ccompl (Class.cv alpha_dummy_021))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_022))).fv) := by
    apply Finset.mem_union_right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0029 : alpha_dummy_025 ∈ (((syn_ccompl (Class.cv alpha_dummy_024))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_025))).fv) := by
    apply Finset.mem_union_right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0030 : alpha_dummy_022 ∈ (((Class.cv alpha_dummy_022)).fv ∪ ((Class.cv alpha_dummy_022)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0031 : alpha_dummy_025 ∈ (((Class.cv alpha_dummy_025)).fv ∪ ((Class.cv alpha_dummy_025)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0032 : alpha_dummy_002 ∈ (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) := by
    apply Finset.mem_union_right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0033 : alpha_dummy_002 ∈ (((syn_ccompl (Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_001) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cphi (Class.cv alpha_dummy_007))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_002) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cun (syn_cphi (Class.cv alpha_dummy_007)) (syn_csn (syn_c0c)))))))).fv) := by
    apply Finset.mem_union_right
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
    ·
      rw [fv_syn_wrex]
      apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 1))
      ·
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0034 : y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
    apply Finset.mem_union_right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0035 : y ∈ (((syn_ccompl (Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv x) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cphi (Class.cv alpha_dummy_009))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv y) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cun (syn_cphi (Class.cv alpha_dummy_009)) (syn_csn (syn_c0c)))))))).fv) := by
    apply Finset.mem_union_right
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0))
    ·
      rw [fv_syn_wrex]
      apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 1))
      ·
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0036 : alpha_dummy_002 ∈ (((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_002) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cun (syn_cphi (Class.cv alpha_dummy_007)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_002) (Wff.classEq (Class.cv alpha_dummy_006) (syn_cun (syn_cphi (Class.cv alpha_dummy_007)) (syn_csn (syn_c0c))))))).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
    ·
      rw [fv_syn_wrex]
      apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 1))
      ·
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0037 : y ∈ (((Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv y) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cun (syn_cphi (Class.cv alpha_dummy_009)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab alpha_dummy_008 (syn_wrex alpha_dummy_009 (Class.cv y) (Wff.classEq (Class.cv alpha_dummy_008) (syn_cun (syn_cphi (Class.cv alpha_dummy_009)) (syn_csn (syn_c0c))))))).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0))
    ·
      rw [fv_syn_wrex]
      apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 1))
      ·
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0038 : alpha_dummy_007 ∈ (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_007)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_ccompl]
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0039 : alpha_dummy_009 ∈ (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_009)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_ccompl]
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0040 : alpha_dummy_007 ∈ (((syn_cphi (Class.cv alpha_dummy_007))).fv ∪ ((syn_cphi (Class.cv alpha_dummy_007))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0041 : alpha_dummy_009 ∈ (((syn_cphi (Class.cv alpha_dummy_009))).fv ∪ ((syn_cphi (Class.cv alpha_dummy_009))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0042 : alpha_dummy_003 ∈ (((Class.cv alpha_dummy_003)).fv ∪ ((Class.cv alpha_dummy_000)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0043 : alpha_dummy_003 ∈ (((syn_ccompl (Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cphi (Class.cv alpha_dummy_043))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c)))))))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 0))
    ·
      rw [fv_syn_wrex]
      apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 1))
      ·
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0044 : z ∈ (((Class.cv z)).fv ∪ ((Class.cv w)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0045 : z ∈ (((syn_ccompl (Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cphi (Class.cv alpha_dummy_045))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cun (syn_cphi (Class.cv alpha_dummy_045)) (syn_csn (syn_c0c)))))))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0044 0))
    ·
      rw [fv_syn_wrex]
      apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0044 1))
      ·
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0046 : alpha_dummy_003 ∈ (((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cphi (Class.cv alpha_dummy_043)))))).fv ∪ ((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cphi (Class.cv alpha_dummy_043)))))).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 0))
    ·
      rw [fv_syn_wrex]
      apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 1))
      ·
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0047 : z ∈ (((Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cphi (Class.cv alpha_dummy_045)))))).fv ∪ ((Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cphi (Class.cv alpha_dummy_045)))))).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0044 0))
    ·
      rw [fv_syn_wrex]
      apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0044 1))
      ·
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0048 : alpha_dummy_043 ∈ (((Class.cv alpha_dummy_043)).fv) := by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0049 : alpha_dummy_045 ∈ (((Class.cv alpha_dummy_045)).fv) := by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0050 : alpha_dummy_050 ∈ (((Wff.classMem (Class.cv alpha_dummy_050) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv alpha_dummy_050) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_050)).fv) := by
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    rw [fv_wff_classMem]
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0051 : alpha_dummy_052 ∈ (((Wff.classMem (Class.cv alpha_dummy_052) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv alpha_dummy_052) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_052)).fv) := by
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    rw [fv_wff_classMem]
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0052 : alpha_dummy_050 ∈ (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0053 : alpha_dummy_052 ∈ (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0054 : alpha_dummy_057 ∈ (((syn_cnin (Class.cv alpha_dummy_057) (Class.cv alpha_dummy_058))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_057) (Class.cv alpha_dummy_058))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_cnin]
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0055 : alpha_dummy_060 ∈ (((syn_cnin (Class.cv alpha_dummy_060) (Class.cv alpha_dummy_061))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_060) (Class.cv alpha_dummy_061))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_cnin]
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0056 : alpha_dummy_057 ∈ (((Class.cv alpha_dummy_057)).fv ∪ ((Class.cv alpha_dummy_058)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0057 : alpha_dummy_060 ∈ (((Class.cv alpha_dummy_060)).fv ∪ ((Class.cv alpha_dummy_061)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0058 : alpha_dummy_058 ∈ (((syn_cnin (Class.cv alpha_dummy_057) (Class.cv alpha_dummy_058))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_057) (Class.cv alpha_dummy_058))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_cnin]
    apply Finset.mem_union_right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0059 : alpha_dummy_061 ∈ (((syn_cnin (Class.cv alpha_dummy_060) (Class.cv alpha_dummy_061))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_060) (Class.cv alpha_dummy_061))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_cnin]
    apply Finset.mem_union_right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0060 : alpha_dummy_058 ∈ (((Class.cv alpha_dummy_057)).fv ∪ ((Class.cv alpha_dummy_058)).fv) := by
    apply Finset.mem_union_right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0061 : alpha_dummy_061 ∈ (((Class.cv alpha_dummy_060)).fv ∪ ((Class.cv alpha_dummy_061)).fv) := by
    apply Finset.mem_union_right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0062 : alpha_dummy_057 ∈ (((syn_ccompl (Class.cv alpha_dummy_057))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_058))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0063 : alpha_dummy_060 ∈ (((syn_ccompl (Class.cv alpha_dummy_060))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_061))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0064 : alpha_dummy_057 ∈ (((Class.cv alpha_dummy_057)).fv ∪ ((Class.cv alpha_dummy_057)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0065 : alpha_dummy_060 ∈ (((Class.cv alpha_dummy_060)).fv ∪ ((Class.cv alpha_dummy_060)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0066 : alpha_dummy_058 ∈ (((syn_ccompl (Class.cv alpha_dummy_057))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_058))).fv) := by
    apply Finset.mem_union_right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0067 : alpha_dummy_061 ∈ (((syn_ccompl (Class.cv alpha_dummy_060))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_061))).fv) := by
    apply Finset.mem_union_right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0068 : alpha_dummy_058 ∈ (((Class.cv alpha_dummy_058)).fv ∪ ((Class.cv alpha_dummy_058)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0069 : alpha_dummy_061 ∈ (((Class.cv alpha_dummy_061)).fv ∪ ((Class.cv alpha_dummy_061)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0070 : alpha_dummy_000 ∈ (((Class.cv alpha_dummy_003)).fv ∪ ((Class.cv alpha_dummy_000)).fv) := by
    apply Finset.mem_union_right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0071 : alpha_dummy_000 ∈ (((syn_ccompl (Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cphi (Class.cv alpha_dummy_043))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c)))))))).fv) := by
    apply Finset.mem_union_right
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 0))
    ·
      rw [fv_syn_wrex]
      apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 1))
      ·
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0072 : w ∈ (((Class.cv z)).fv ∪ ((Class.cv w)).fv) := by
    apply Finset.mem_union_right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0073 : w ∈ (((syn_ccompl (Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cphi (Class.cv alpha_dummy_045))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cun (syn_cphi (Class.cv alpha_dummy_045)) (syn_csn (syn_c0c)))))))).fv) := by
    apply Finset.mem_union_right
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0072 0))
    ·
      rw [fv_syn_wrex]
      apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0072 1))
      ·
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0074 : alpha_dummy_000 ∈ (((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c))))))).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 0))
    ·
      rw [fv_syn_wrex]
      apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 1))
      ·
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0075 : w ∈ (((Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cun (syn_cphi (Class.cv alpha_dummy_045)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cun (syn_cphi (Class.cv alpha_dummy_045)) (syn_csn (syn_c0c))))))).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0072 0))
    ·
      rw [fv_syn_wrex]
      apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0072 1))
      ·
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0076 : alpha_dummy_043 ∈ (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_043)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_ccompl]
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0077 : alpha_dummy_045 ∈ (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_045)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_ccompl]
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0078 : alpha_dummy_043 ∈ (((syn_cphi (Class.cv alpha_dummy_043))).fv ∪ ((syn_cphi (Class.cv alpha_dummy_043))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0079 : alpha_dummy_045 ∈ (((syn_cphi (Class.cv alpha_dummy_045))).fv ∪ ((syn_cphi (Class.cv alpha_dummy_045))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0080 : alpha_dummy_000 ∈ (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_003)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0081 : alpha_dummy_000 ∈ (((syn_ccompl (Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cphi (Class.cv alpha_dummy_079))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cun (syn_cphi (Class.cv alpha_dummy_079)) (syn_csn (syn_c0c)))))))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0080 0))
    ·
      rw [fv_syn_wrex]
      apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0080 1))
      ·
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0082 : w ∈ (((Class.cv w)).fv ∪ ((Class.cv z)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0083 : w ∈ (((syn_ccompl (Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cphi (Class.cv alpha_dummy_081))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cun (syn_cphi (Class.cv alpha_dummy_081)) (syn_csn (syn_c0c)))))))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0082 0))
    ·
      rw [fv_syn_wrex]
      apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0082 1))
      ·
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0084 : alpha_dummy_000 ∈ (((Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cphi (Class.cv alpha_dummy_079)))))).fv ∪ ((Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cphi (Class.cv alpha_dummy_079)))))).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0080 0))
    ·
      rw [fv_syn_wrex]
      apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0080 1))
      ·
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0085 : w ∈ (((Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cphi (Class.cv alpha_dummy_081)))))).fv ∪ ((Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cphi (Class.cv alpha_dummy_081)))))).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0082 0))
    ·
      rw [fv_syn_wrex]
      apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0082 1))
      ·
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0086 : alpha_dummy_079 ∈ (((Class.cv alpha_dummy_079)).fv) := by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0087 : alpha_dummy_081 ∈ (((Class.cv alpha_dummy_081)).fv) := by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0088 : alpha_dummy_086 ∈ (((Wff.classMem (Class.cv alpha_dummy_086) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv alpha_dummy_086) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_086)).fv) := by
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    rw [fv_wff_classMem]
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0089 : alpha_dummy_088 ∈ (((Wff.classMem (Class.cv alpha_dummy_088) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv alpha_dummy_088) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_088)).fv) := by
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    rw [fv_wff_classMem]
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0090 : alpha_dummy_086 ∈ (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0091 : alpha_dummy_088 ∈ (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0092 : alpha_dummy_093 ∈ (((syn_cnin (Class.cv alpha_dummy_093) (Class.cv alpha_dummy_094))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_093) (Class.cv alpha_dummy_094))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_cnin]
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0093 : alpha_dummy_096 ∈ (((syn_cnin (Class.cv alpha_dummy_096) (Class.cv alpha_dummy_097))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_096) (Class.cv alpha_dummy_097))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_cnin]
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0094 : alpha_dummy_093 ∈ (((Class.cv alpha_dummy_093)).fv ∪ ((Class.cv alpha_dummy_094)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0095 : alpha_dummy_096 ∈ (((Class.cv alpha_dummy_096)).fv ∪ ((Class.cv alpha_dummy_097)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0096 : alpha_dummy_094 ∈ (((syn_cnin (Class.cv alpha_dummy_093) (Class.cv alpha_dummy_094))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_093) (Class.cv alpha_dummy_094))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_cnin]
    apply Finset.mem_union_right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0097 : alpha_dummy_097 ∈ (((syn_cnin (Class.cv alpha_dummy_096) (Class.cv alpha_dummy_097))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_096) (Class.cv alpha_dummy_097))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_cnin]
    apply Finset.mem_union_right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0098 : alpha_dummy_094 ∈ (((Class.cv alpha_dummy_093)).fv ∪ ((Class.cv alpha_dummy_094)).fv) := by
    apply Finset.mem_union_right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0099 : alpha_dummy_097 ∈ (((Class.cv alpha_dummy_096)).fv ∪ ((Class.cv alpha_dummy_097)).fv) := by
    apply Finset.mem_union_right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0100 : alpha_dummy_093 ∈ (((syn_ccompl (Class.cv alpha_dummy_093))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_094))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0101 : alpha_dummy_096 ∈ (((syn_ccompl (Class.cv alpha_dummy_096))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_097))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0102 : alpha_dummy_093 ∈ (((Class.cv alpha_dummy_093)).fv ∪ ((Class.cv alpha_dummy_093)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0103 : alpha_dummy_096 ∈ (((Class.cv alpha_dummy_096)).fv ∪ ((Class.cv alpha_dummy_096)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0104 : alpha_dummy_094 ∈ (((syn_ccompl (Class.cv alpha_dummy_093))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_094))).fv) := by
    apply Finset.mem_union_right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0105 : alpha_dummy_097 ∈ (((syn_ccompl (Class.cv alpha_dummy_096))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_097))).fv) := by
    apply Finset.mem_union_right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0106 : alpha_dummy_094 ∈ (((Class.cv alpha_dummy_094)).fv ∪ ((Class.cv alpha_dummy_094)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0107 : alpha_dummy_097 ∈ (((Class.cv alpha_dummy_097)).fv ∪ ((Class.cv alpha_dummy_097)).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0108 : alpha_dummy_003 ∈ (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_003)).fv) := by
    apply Finset.mem_union_right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0109 : alpha_dummy_003 ∈ (((syn_ccompl (Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cphi (Class.cv alpha_dummy_079))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cun (syn_cphi (Class.cv alpha_dummy_079)) (syn_csn (syn_c0c)))))))).fv) := by
    apply Finset.mem_union_right
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0108 0))
    ·
      rw [fv_syn_wrex]
      apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0108 1))
      ·
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0110 : z ∈ (((Class.cv w)).fv ∪ ((Class.cv z)).fv) := by
    apply Finset.mem_union_right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0111 : z ∈ (((syn_ccompl (Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cphi (Class.cv alpha_dummy_081))))))).fv ∪ ((syn_ccompl (Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cun (syn_cphi (Class.cv alpha_dummy_081)) (syn_csn (syn_c0c)))))))).fv) := by
    apply Finset.mem_union_right
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0110 0))
    ·
      rw [fv_syn_wrex]
      apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0110 1))
      ·
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0112 : alpha_dummy_003 ∈ (((Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cun (syn_cphi (Class.cv alpha_dummy_079)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cun (syn_cphi (Class.cv alpha_dummy_079)) (syn_csn (syn_c0c))))))).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0108 0))
    ·
      rw [fv_syn_wrex]
      apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0108 1))
      ·
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0113 : z ∈ (((Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cun (syn_cphi (Class.cv alpha_dummy_081)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cun (syn_cphi (Class.cv alpha_dummy_081)) (syn_csn (syn_c0c))))))).fv) := by
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0110 0))
    ·
      rw [fv_syn_wrex]
      apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0110 1))
      ·
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0114 : alpha_dummy_079 ∈ (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_079)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_ccompl]
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0115 : alpha_dummy_081 ∈ (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_081)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_ccompl]
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0116 : alpha_dummy_079 ∈ (((syn_cphi (Class.cv alpha_dummy_079))).fv ∪ ((syn_cphi (Class.cv alpha_dummy_079))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0117 : alpha_dummy_081 ∈ (((syn_cphi (Class.cv alpha_dummy_081))).fv ∪ ((syn_cphi (Class.cv alpha_dummy_081))).fv) := by
    apply Finset.mem_union_left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have wpp_notmem_0000 : alpha_dummy_004 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0001 : alpha_dummy_005 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0002 : alpha_dummy_001 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0003 : x ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0004 : alpha_dummy_002 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0005 : y ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0006 : alpha_dummy_010 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0007 : alpha_dummy_011 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0008 : alpha_dummy_012 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0009 : alpha_dummy_013 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0010 : alpha_dummy_006 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0011 : alpha_dummy_008 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0012 : alpha_dummy_007 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0013 : alpha_dummy_009 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0014 : alpha_dummy_015 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0015 : alpha_dummy_017 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0016 : alpha_dummy_014 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0017 : alpha_dummy_016 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0018 : alpha_dummy_018 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0019 : alpha_dummy_019 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0020 : alpha_dummy_020 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0021 : alpha_dummy_023 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0022 : alpha_dummy_021 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0023 : alpha_dummy_024 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0024 : alpha_dummy_022 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0025 : alpha_dummy_025 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0000 : TReflOn [(alpha_dummy_022, alpha_dummy_025), (alpha_dummy_021, alpha_dummy_024), (alpha_dummy_020, alpha_dummy_023), (alpha_dummy_018, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_016), (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_012, alpha_dummy_013), (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] ((syn_c1c)).fv := by
    intro u hu
    exact (TAlphaVar.there (fun h_eq => (wpp_notmem_0024) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0025) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0022) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0023) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0020) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0021) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0018) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0019) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0016) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0017) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0014) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0015) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0012) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0013) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0010) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0011) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0008) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0009) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0006) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0007) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0004) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0005) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0002) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0003) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0000) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0001) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp)))))))))))))))
  have wpp_notmem_0026 : alpha_dummy_004 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0027 : alpha_dummy_005 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0028 : alpha_dummy_001 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0029 : x ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0030 : alpha_dummy_002 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0031 : y ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0032 : alpha_dummy_010 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0033 : alpha_dummy_011 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0034 : alpha_dummy_012 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0035 : alpha_dummy_013 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0036 : alpha_dummy_006 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0037 : alpha_dummy_008 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0038 : alpha_dummy_007 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0039 : alpha_dummy_009 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0040 : alpha_dummy_015 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0041 : alpha_dummy_017 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0042 : alpha_dummy_014 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0043 : alpha_dummy_016 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0044 : alpha_dummy_018 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0045 : alpha_dummy_019 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0046 : alpha_dummy_020 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0047 : alpha_dummy_023 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0048 : alpha_dummy_021 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0049 : alpha_dummy_024 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0050 : alpha_dummy_022 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0051 : alpha_dummy_025 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0001 : TReflOn [(alpha_dummy_022, alpha_dummy_025), (alpha_dummy_021, alpha_dummy_024), (alpha_dummy_020, alpha_dummy_023), (alpha_dummy_018, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_016), (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_012, alpha_dummy_013), (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] ((syn_c0)).fv := by
    intro u hu
    exact (TAlphaVar.there (fun h_eq => (wpp_notmem_0050) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0051) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0048) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0049) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0046) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0047) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0044) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0045) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0042) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0043) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0040) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0041) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0038) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0039) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0036) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0037) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0034) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0035) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0032) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0033) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0030) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0031) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0028) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0029) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0026) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0027) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp)))))))))))))))
  have split_alpha_0000 : TAlphaWff [(alpha_dummy_022, alpha_dummy_025), (alpha_dummy_021, alpha_dummy_024), (alpha_dummy_020, alpha_dummy_023), (alpha_dummy_018, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_016), (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_012, alpha_dummy_013), (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_021) (Class.cv alpha_dummy_022)) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_020) (syn_cun (Class.cv alpha_dummy_021) (Class.cv alpha_dummy_022))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_024) (Class.cv alpha_dummy_025)) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_023) (syn_cun (Class.cv alpha_dummy_024) (Class.cv alpha_dummy_025))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [(alpha_dummy_022, alpha_dummy_025), (alpha_dummy_021, alpha_dummy_024), (alpha_dummy_020, alpha_dummy_023), (alpha_dummy_018, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_016), (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_012, alpha_dummy_013), (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_c0) wpp_refl_0001)) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0)) (TAlphaVar.here _ _ _)))))))))))))))))))
  have wpp_notmem_0052 : alpha_dummy_004 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0053 : alpha_dummy_005 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0054 : alpha_dummy_001 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0055 : x ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0056 : alpha_dummy_002 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0057 : y ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0058 : alpha_dummy_010 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0059 : alpha_dummy_011 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0060 : alpha_dummy_012 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0061 : alpha_dummy_013 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0062 : alpha_dummy_006 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0063 : alpha_dummy_008 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0064 : alpha_dummy_007 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0065 : alpha_dummy_009 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0066 : alpha_dummy_015 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0067 : alpha_dummy_017 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0068 : alpha_dummy_014 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0069 : alpha_dummy_016 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0070 : alpha_dummy_018 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0071 : alpha_dummy_019 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0002 : TReflOn [(alpha_dummy_018, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_016), (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_012, alpha_dummy_013), (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] ((syn_cnnc)).fv := by
    intro u hu
    exact (TAlphaVar.there (fun h_eq => (wpp_notmem_0070) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0071) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0068) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0069) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0066) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0067) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0064) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0065) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0062) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0063) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0060) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0061) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0058) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0059) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0056) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0057) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0054) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0055) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0052) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0053) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp))))))))))))
  have split_alpha_0001 : TAlphaWff [(alpha_dummy_007, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_012, alpha_dummy_013), (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (Wff.imp (Wff.classMem (Class.cv alpha_dummy_007) (Class.cv alpha_dummy_001)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_006) (syn_cphi (Class.cv alpha_dummy_007))))) (Wff.imp (Wff.classMem (Class.cv alpha_dummy_009) (Class.cv x)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_008) (syn_cphi (Class.cv alpha_dummy_009))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_007)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_009)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [(alpha_dummy_022, alpha_dummy_025), (alpha_dummy_021, alpha_dummy_024), (alpha_dummy_020, alpha_dummy_023), (alpha_dummy_018, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_016), (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_012, alpha_dummy_013), (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_c1c) wpp_refl_0000)) (TAlphaWff.neg (TAlphaWff.neg split_alpha_0000))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [(alpha_dummy_018, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_016), (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_012, alpha_dummy_013), (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_cnnc) wpp_refl_0002)))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [(alpha_dummy_018, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_016), (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_012, alpha_dummy_013), (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_cnnc) wpp_refl_0002)))))))))))))))))))
  have wpp_notmem_0072 : alpha_dummy_036 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0073 : alpha_dummy_037 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0074 : alpha_dummy_038 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0075 : alpha_dummy_039 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0076 : alpha_dummy_040 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0077 : alpha_dummy_041 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0003 : TReflOn [(alpha_dummy_022, alpha_dummy_025), (alpha_dummy_021, alpha_dummy_024), (alpha_dummy_020, alpha_dummy_023), (alpha_dummy_018, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_016), (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_040, alpha_dummy_041), (alpha_dummy_038, alpha_dummy_039), (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_036, alpha_dummy_037), (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] ((syn_c1c)).fv := by
    intro u hu
    exact (TAlphaVar.there (fun h_eq => (wpp_notmem_0024) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0025) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0022) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0023) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0020) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0021) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0018) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0019) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0016) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0017) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0014) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0015) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0076) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0077) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0074) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0075) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0012) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0013) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0010) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0011) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0072) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0073) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0006) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0007) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0004) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0005) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0002) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0003) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0000) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0001) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp)))))))))))))))))
  have wpp_notmem_0078 : alpha_dummy_036 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0079 : alpha_dummy_037 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0080 : alpha_dummy_038 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0081 : alpha_dummy_039 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0082 : alpha_dummy_040 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0083 : alpha_dummy_041 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0004 : TReflOn [(alpha_dummy_022, alpha_dummy_025), (alpha_dummy_021, alpha_dummy_024), (alpha_dummy_020, alpha_dummy_023), (alpha_dummy_018, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_016), (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_040, alpha_dummy_041), (alpha_dummy_038, alpha_dummy_039), (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_036, alpha_dummy_037), (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] ((syn_c0)).fv := by
    intro u hu
    exact (TAlphaVar.there (fun h_eq => (wpp_notmem_0050) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0051) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0048) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0049) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0046) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0047) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0044) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0045) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0042) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0043) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0040) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0041) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0082) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0083) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0080) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0081) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0038) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0039) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0036) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0037) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0078) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0079) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0032) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0033) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0030) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0031) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0028) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0029) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0026) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0027) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp)))))))))))))))))
  have split_alpha_0002 : TAlphaWff [(alpha_dummy_022, alpha_dummy_025), (alpha_dummy_021, alpha_dummy_024), (alpha_dummy_020, alpha_dummy_023), (alpha_dummy_018, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_016), (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_040, alpha_dummy_041), (alpha_dummy_038, alpha_dummy_039), (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_036, alpha_dummy_037), (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_021) (Class.cv alpha_dummy_022)) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_020) (syn_cun (Class.cv alpha_dummy_021) (Class.cv alpha_dummy_022))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_024) (Class.cv alpha_dummy_025)) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_023) (syn_cun (Class.cv alpha_dummy_024) (Class.cv alpha_dummy_025))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [(alpha_dummy_022, alpha_dummy_025), (alpha_dummy_021, alpha_dummy_024), (alpha_dummy_020, alpha_dummy_023), (alpha_dummy_018, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_016), (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_040, alpha_dummy_041), (alpha_dummy_038, alpha_dummy_039), (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_036, alpha_dummy_037), (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_c0) wpp_refl_0004)) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_016)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0)) (TAlphaVar.here _ _ _)))))))))))))))))))
  have wpp_notmem_0084 : alpha_dummy_036 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0085 : alpha_dummy_037 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0086 : alpha_dummy_038 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0087 : alpha_dummy_039 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0088 : alpha_dummy_040 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0089 : alpha_dummy_041 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0005 : TReflOn [(alpha_dummy_018, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_016), (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_040, alpha_dummy_041), (alpha_dummy_038, alpha_dummy_039), (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_036, alpha_dummy_037), (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] ((syn_cnnc)).fv := by
    intro u hu
    exact (TAlphaVar.there (fun h_eq => (wpp_notmem_0070) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0071) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0068) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0069) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0066) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0067) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0088) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0089) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0086) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0087) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0064) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0065) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0062) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0063) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0084) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0085) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0058) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0059) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0056) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0057) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0054) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0055) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0052) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0053) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp))))))))))))))
  have split_alpha_0003 : TAlphaWff [(alpha_dummy_040, alpha_dummy_041), (alpha_dummy_038, alpha_dummy_039), (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_036, alpha_dummy_037), (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (Wff.imp (Wff.classMem (Class.cv alpha_dummy_040) (syn_cphi (Class.cv alpha_dummy_007))) (Wff.neg (Wff.classMem (Class.cv alpha_dummy_040) (syn_cphi (Class.cv alpha_dummy_007))))) (Wff.imp (Wff.classMem (Class.cv alpha_dummy_041) (syn_cphi (Class.cv alpha_dummy_009))) (Wff.neg (Wff.classMem (Class.cv alpha_dummy_041) (syn_cphi (Class.cv alpha_dummy_009))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0040 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0041 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0038 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0039 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_007)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_009)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [(alpha_dummy_022, alpha_dummy_025), (alpha_dummy_021, alpha_dummy_024), (alpha_dummy_020, alpha_dummy_023), (alpha_dummy_018, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_016), (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_040, alpha_dummy_041), (alpha_dummy_038, alpha_dummy_039), (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_036, alpha_dummy_037), (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_c1c) wpp_refl_0003)) (TAlphaWff.neg (TAlphaWff.neg split_alpha_0002))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [(alpha_dummy_018, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_016), (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_040, alpha_dummy_041), (alpha_dummy_038, alpha_dummy_039), (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_036, alpha_dummy_037), (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_cnnc) wpp_refl_0005)))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [(alpha_dummy_018, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_016), (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_040, alpha_dummy_041), (alpha_dummy_038, alpha_dummy_039), (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_036, alpha_dummy_037), (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_cnnc) wpp_refl_0005))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0040 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0041 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0038 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0039 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_007)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_009)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [(alpha_dummy_022, alpha_dummy_025), (alpha_dummy_021, alpha_dummy_024), (alpha_dummy_020, alpha_dummy_023), (alpha_dummy_018, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_016), (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_040, alpha_dummy_041), (alpha_dummy_038, alpha_dummy_039), (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_036, alpha_dummy_037), (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_c1c) wpp_refl_0003)) (TAlphaWff.neg (TAlphaWff.neg split_alpha_0002))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [(alpha_dummy_018, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_016), (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_040, alpha_dummy_041), (alpha_dummy_038, alpha_dummy_039), (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_036, alpha_dummy_037), (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_cnnc) wpp_refl_0005)))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [(alpha_dummy_018, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_016), (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_040, alpha_dummy_041), (alpha_dummy_038, alpha_dummy_039), (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_036, alpha_dummy_037), (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_cnnc) wpp_refl_0005)))))))))))))))))))
  have wpp_notmem_0090 : alpha_dummy_004 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0091 : alpha_dummy_005 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0092 : alpha_dummy_001 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0093 : x ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0094 : alpha_dummy_002 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0095 : y ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0096 : alpha_dummy_010 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0097 : alpha_dummy_011 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0098 : alpha_dummy_036 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0099 : alpha_dummy_037 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0100 : alpha_dummy_006 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0101 : alpha_dummy_008 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0102 : alpha_dummy_007 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0103 : alpha_dummy_009 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0104 : alpha_dummy_038 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0105 : alpha_dummy_039 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_refl_0006 : TReflOn [(alpha_dummy_038, alpha_dummy_039), (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_036, alpha_dummy_037), (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    intro u hu
    exact (TAlphaVar.there (fun h_eq => (wpp_notmem_0104) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0105) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0102) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0103) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0100) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0101) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0098) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0099) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0096) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0097) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0094) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0095) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0092) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0093) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0090) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0091) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp))))))))))
  have split_alpha_0004 : TAlphaWff [(alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (Wff.classEq (Class.cv alpha_dummy_004) (syn_cop (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))) (Wff.classEq (Class.cv alpha_dummy_005) (syn_cop (Class.cv x) (Class.cv y))) :=
    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))) (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg split_alpha_0001)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg split_alpha_0001)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0037 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0035 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg split_alpha_0003)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [(alpha_dummy_038, alpha_dummy_039), (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_036, alpha_dummy_037), (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_ccompl (syn_csn (syn_c0c))) wpp_refl_0006)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0037 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0035 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg split_alpha_0003)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [(alpha_dummy_038, alpha_dummy_039), (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_036, alpha_dummy_037), (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_ccompl (syn_csn (syn_c0c))) wpp_refl_0006))))))))))))))))))))))))))))
  have wpp_notmem_0106 : alpha_dummy_003 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0107 : z ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0108 : alpha_dummy_000 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0109 : w ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0110 : alpha_dummy_046 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0111 : alpha_dummy_047 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0112 : alpha_dummy_048 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0113 : alpha_dummy_049 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0114 : alpha_dummy_042 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0115 : alpha_dummy_044 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0116 : alpha_dummy_043 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0117 : alpha_dummy_045 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0118 : alpha_dummy_051 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0119 : alpha_dummy_053 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0120 : alpha_dummy_050 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0121 : alpha_dummy_052 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0122 : alpha_dummy_054 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0123 : alpha_dummy_055 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0124 : alpha_dummy_056 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0125 : alpha_dummy_059 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0126 : alpha_dummy_057 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0127 : alpha_dummy_060 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0128 : alpha_dummy_058 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0129 : alpha_dummy_061 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0007 : TReflOn [(alpha_dummy_058, alpha_dummy_061), (alpha_dummy_057, alpha_dummy_060), (alpha_dummy_056, alpha_dummy_059), (alpha_dummy_054, alpha_dummy_055), (alpha_dummy_050, alpha_dummy_052), (alpha_dummy_051, alpha_dummy_053), (alpha_dummy_043, alpha_dummy_045), (alpha_dummy_042, alpha_dummy_044), (alpha_dummy_048, alpha_dummy_049), (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] ((syn_c1c)).fv := by
    intro u hu
    exact (TAlphaVar.there (fun h_eq => (wpp_notmem_0128) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0129) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0126) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0127) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0124) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0125) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0122) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0123) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0120) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0121) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0118) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0119) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0116) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0117) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0114) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0115) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0112) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0113) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0110) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0111) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0108) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0109) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0106) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0107) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0004) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0005) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0002) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0003) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0000) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0001) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp)))))))))))))))))
  have wpp_notmem_0130 : alpha_dummy_003 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0131 : z ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0132 : alpha_dummy_000 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0133 : w ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0134 : alpha_dummy_046 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0135 : alpha_dummy_047 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0136 : alpha_dummy_048 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0137 : alpha_dummy_049 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0138 : alpha_dummy_042 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0139 : alpha_dummy_044 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0140 : alpha_dummy_043 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0141 : alpha_dummy_045 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0142 : alpha_dummy_051 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0143 : alpha_dummy_053 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0144 : alpha_dummy_050 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0145 : alpha_dummy_052 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0146 : alpha_dummy_054 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0147 : alpha_dummy_055 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0148 : alpha_dummy_056 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0149 : alpha_dummy_059 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0150 : alpha_dummy_057 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0151 : alpha_dummy_060 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0152 : alpha_dummy_058 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0153 : alpha_dummy_061 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0008 : TReflOn [(alpha_dummy_058, alpha_dummy_061), (alpha_dummy_057, alpha_dummy_060), (alpha_dummy_056, alpha_dummy_059), (alpha_dummy_054, alpha_dummy_055), (alpha_dummy_050, alpha_dummy_052), (alpha_dummy_051, alpha_dummy_053), (alpha_dummy_043, alpha_dummy_045), (alpha_dummy_042, alpha_dummy_044), (alpha_dummy_048, alpha_dummy_049), (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] ((syn_c0)).fv := by
    intro u hu
    exact (TAlphaVar.there (fun h_eq => (wpp_notmem_0152) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0153) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0150) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0151) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0148) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0149) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0146) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0147) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0144) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0145) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0142) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0143) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0140) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0141) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0138) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0139) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0136) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0137) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0134) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0135) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0132) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0133) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0130) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0131) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0030) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0031) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0028) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0029) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0026) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0027) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp)))))))))))))))))
  have split_alpha_0005 : TAlphaWff [(alpha_dummy_058, alpha_dummy_061), (alpha_dummy_057, alpha_dummy_060), (alpha_dummy_056, alpha_dummy_059), (alpha_dummy_054, alpha_dummy_055), (alpha_dummy_050, alpha_dummy_052), (alpha_dummy_051, alpha_dummy_053), (alpha_dummy_043, alpha_dummy_045), (alpha_dummy_042, alpha_dummy_044), (alpha_dummy_048, alpha_dummy_049), (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_057) (Class.cv alpha_dummy_058)) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_056) (syn_cun (Class.cv alpha_dummy_057) (Class.cv alpha_dummy_058))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_060) (Class.cv alpha_dummy_061)) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_059) (syn_cun (Class.cv alpha_dummy_060) (Class.cv alpha_dummy_061))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0057 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0055 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0061 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0059 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0057 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0055 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0061 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0059 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [(alpha_dummy_058, alpha_dummy_061), (alpha_dummy_057, alpha_dummy_060), (alpha_dummy_056, alpha_dummy_059), (alpha_dummy_054, alpha_dummy_055), (alpha_dummy_050, alpha_dummy_052), (alpha_dummy_051, alpha_dummy_053), (alpha_dummy_043, alpha_dummy_045), (alpha_dummy_042, alpha_dummy_044), (alpha_dummy_048, alpha_dummy_049), (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_c0) wpp_refl_0008)) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0065 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0063 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0065 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0063 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0069 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0067 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0069 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0067 0)) (TAlphaVar.here _ _ _)))))))))))))))))))
  have wpp_notmem_0154 : alpha_dummy_003 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0155 : z ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0156 : alpha_dummy_000 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0157 : w ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0158 : alpha_dummy_046 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0159 : alpha_dummy_047 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0160 : alpha_dummy_048 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0161 : alpha_dummy_049 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0162 : alpha_dummy_042 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0163 : alpha_dummy_044 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0164 : alpha_dummy_043 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0165 : alpha_dummy_045 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0166 : alpha_dummy_051 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0167 : alpha_dummy_053 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0168 : alpha_dummy_050 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0169 : alpha_dummy_052 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0170 : alpha_dummy_054 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0171 : alpha_dummy_055 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0009 : TReflOn [(alpha_dummy_054, alpha_dummy_055), (alpha_dummy_050, alpha_dummy_052), (alpha_dummy_051, alpha_dummy_053), (alpha_dummy_043, alpha_dummy_045), (alpha_dummy_042, alpha_dummy_044), (alpha_dummy_048, alpha_dummy_049), (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] ((syn_cnnc)).fv := by
    intro u hu
    exact (TAlphaVar.there (fun h_eq => (wpp_notmem_0170) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0171) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0168) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0169) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0166) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0167) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0164) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0165) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0162) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0163) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0160) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0161) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0158) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0159) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0156) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0157) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0154) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0155) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0056) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0057) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0054) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0055) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0052) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0053) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp))))))))))))))
  have split_alpha_0006 : TAlphaWff [(alpha_dummy_043, alpha_dummy_045), (alpha_dummy_042, alpha_dummy_044), (alpha_dummy_048, alpha_dummy_049), (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (Wff.imp (Wff.classMem (Class.cv alpha_dummy_043) (Class.cv alpha_dummy_003)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_042) (syn_cphi (Class.cv alpha_dummy_043))))) (Wff.imp (Wff.classMem (Class.cv alpha_dummy_045) (Class.cv z)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_044) (syn_cphi (Class.cv alpha_dummy_045))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0044 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0044 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0046 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0047 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0043 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0045 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) (Ne.symm dv_w_z) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_003)).fv ∪ ((Class.cv alpha_dummy_000)).fv) (by decide)) (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv w)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0049 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0049 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_043)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_045)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0053 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0053 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [(alpha_dummy_058, alpha_dummy_061), (alpha_dummy_057, alpha_dummy_060), (alpha_dummy_056, alpha_dummy_059), (alpha_dummy_054, alpha_dummy_055), (alpha_dummy_050, alpha_dummy_052), (alpha_dummy_051, alpha_dummy_053), (alpha_dummy_043, alpha_dummy_045), (alpha_dummy_042, alpha_dummy_044), (alpha_dummy_048, alpha_dummy_049), (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_c1c) wpp_refl_0007)) (TAlphaWff.neg (TAlphaWff.neg split_alpha_0005))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [(alpha_dummy_054, alpha_dummy_055), (alpha_dummy_050, alpha_dummy_052), (alpha_dummy_051, alpha_dummy_053), (alpha_dummy_043, alpha_dummy_045), (alpha_dummy_042, alpha_dummy_044), (alpha_dummy_048, alpha_dummy_049), (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_cnnc) wpp_refl_0009)))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [(alpha_dummy_054, alpha_dummy_055), (alpha_dummy_050, alpha_dummy_052), (alpha_dummy_051, alpha_dummy_053), (alpha_dummy_043, alpha_dummy_045), (alpha_dummy_042, alpha_dummy_044), (alpha_dummy_048, alpha_dummy_049), (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_cnnc) wpp_refl_0009)))))))))))))))))))
  have wpp_notmem_0172 : alpha_dummy_072 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0173 : alpha_dummy_073 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0174 : alpha_dummy_074 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0175 : alpha_dummy_075 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0176 : alpha_dummy_076 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0177 : alpha_dummy_077 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0010 : TReflOn [(alpha_dummy_058, alpha_dummy_061), (alpha_dummy_057, alpha_dummy_060), (alpha_dummy_056, alpha_dummy_059), (alpha_dummy_054, alpha_dummy_055), (alpha_dummy_050, alpha_dummy_052), (alpha_dummy_051, alpha_dummy_053), (alpha_dummy_076, alpha_dummy_077), (alpha_dummy_074, alpha_dummy_075), (alpha_dummy_043, alpha_dummy_045), (alpha_dummy_042, alpha_dummy_044), (alpha_dummy_072, alpha_dummy_073), (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] ((syn_c1c)).fv := by
    intro u hu
    exact (TAlphaVar.there (fun h_eq => (wpp_notmem_0128) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0129) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0126) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0127) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0124) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0125) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0122) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0123) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0120) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0121) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0118) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0119) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0176) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0177) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0174) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0175) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0116) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0117) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0114) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0115) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0172) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0173) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0110) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0111) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0108) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0109) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0106) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0107) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0004) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0005) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0002) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0003) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0000) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0001) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp)))))))))))))))))))
  have wpp_notmem_0178 : alpha_dummy_072 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0179 : alpha_dummy_073 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0180 : alpha_dummy_074 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0181 : alpha_dummy_075 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0182 : alpha_dummy_076 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0183 : alpha_dummy_077 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0011 : TReflOn [(alpha_dummy_058, alpha_dummy_061), (alpha_dummy_057, alpha_dummy_060), (alpha_dummy_056, alpha_dummy_059), (alpha_dummy_054, alpha_dummy_055), (alpha_dummy_050, alpha_dummy_052), (alpha_dummy_051, alpha_dummy_053), (alpha_dummy_076, alpha_dummy_077), (alpha_dummy_074, alpha_dummy_075), (alpha_dummy_043, alpha_dummy_045), (alpha_dummy_042, alpha_dummy_044), (alpha_dummy_072, alpha_dummy_073), (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] ((syn_c0)).fv := by
    intro u hu
    exact (TAlphaVar.there (fun h_eq => (wpp_notmem_0152) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0153) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0150) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0151) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0148) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0149) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0146) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0147) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0144) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0145) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0142) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0143) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0182) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0183) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0180) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0181) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0140) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0141) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0138) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0139) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0178) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0179) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0134) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0135) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0132) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0133) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0130) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0131) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0030) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0031) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0028) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0029) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0026) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0027) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp)))))))))))))))))))
  have split_alpha_0007 : TAlphaWff [(alpha_dummy_058, alpha_dummy_061), (alpha_dummy_057, alpha_dummy_060), (alpha_dummy_056, alpha_dummy_059), (alpha_dummy_054, alpha_dummy_055), (alpha_dummy_050, alpha_dummy_052), (alpha_dummy_051, alpha_dummy_053), (alpha_dummy_076, alpha_dummy_077), (alpha_dummy_074, alpha_dummy_075), (alpha_dummy_043, alpha_dummy_045), (alpha_dummy_042, alpha_dummy_044), (alpha_dummy_072, alpha_dummy_073), (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_057) (Class.cv alpha_dummy_058)) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_056) (syn_cun (Class.cv alpha_dummy_057) (Class.cv alpha_dummy_058))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_060) (Class.cv alpha_dummy_061)) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_059) (syn_cun (Class.cv alpha_dummy_060) (Class.cv alpha_dummy_061))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0057 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0055 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0061 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0059 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0057 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0055 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0061 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0059 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [(alpha_dummy_058, alpha_dummy_061), (alpha_dummy_057, alpha_dummy_060), (alpha_dummy_056, alpha_dummy_059), (alpha_dummy_054, alpha_dummy_055), (alpha_dummy_050, alpha_dummy_052), (alpha_dummy_051, alpha_dummy_053), (alpha_dummy_076, alpha_dummy_077), (alpha_dummy_074, alpha_dummy_075), (alpha_dummy_043, alpha_dummy_045), (alpha_dummy_042, alpha_dummy_044), (alpha_dummy_072, alpha_dummy_073), (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_c0) wpp_refl_0011)) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0065 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0063 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0065 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0063 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_052)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0069 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0067 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0069 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0067 0)) (TAlphaVar.here _ _ _)))))))))))))))))))
  have wpp_notmem_0184 : alpha_dummy_072 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0185 : alpha_dummy_073 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0186 : alpha_dummy_074 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0187 : alpha_dummy_075 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0188 : alpha_dummy_076 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0189 : alpha_dummy_077 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0012 : TReflOn [(alpha_dummy_054, alpha_dummy_055), (alpha_dummy_050, alpha_dummy_052), (alpha_dummy_051, alpha_dummy_053), (alpha_dummy_076, alpha_dummy_077), (alpha_dummy_074, alpha_dummy_075), (alpha_dummy_043, alpha_dummy_045), (alpha_dummy_042, alpha_dummy_044), (alpha_dummy_072, alpha_dummy_073), (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] ((syn_cnnc)).fv := by
    intro u hu
    exact (TAlphaVar.there (fun h_eq => (wpp_notmem_0170) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0171) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0168) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0169) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0166) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0167) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0188) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0189) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0186) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0187) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0164) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0165) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0162) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0163) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0184) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0185) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0158) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0159) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0156) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0157) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0154) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0155) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0056) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0057) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0054) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0055) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0052) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0053) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp))))))))))))))))
  have split_alpha_0008 : TAlphaWff [(alpha_dummy_051, alpha_dummy_053), (alpha_dummy_076, alpha_dummy_077), (alpha_dummy_074, alpha_dummy_075), (alpha_dummy_043, alpha_dummy_045), (alpha_dummy_042, alpha_dummy_044), (alpha_dummy_072, alpha_dummy_073), (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (Wff.all alpha_dummy_050 (Wff.neg (syn_wa (Wff.classMem (Class.cv alpha_dummy_050) (Class.cv alpha_dummy_043)) (Wff.classEq (Class.cv alpha_dummy_051) (syn_cif (Wff.classMem (Class.cv alpha_dummy_050) (syn_cnnc)) (syn_cplc (Class.cv alpha_dummy_050) (syn_c1c)) (Class.cv alpha_dummy_050)))))) (Wff.all alpha_dummy_052 (Wff.neg (syn_wa (Wff.classMem (Class.cv alpha_dummy_052) (Class.cv alpha_dummy_045)) (Wff.classEq (Class.cv alpha_dummy_053) (syn_cif (Wff.classMem (Class.cv alpha_dummy_052) (syn_cnnc)) (syn_cplc (Class.cv alpha_dummy_052) (syn_c1c)) (Class.cv alpha_dummy_052)))))) :=
    (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0049 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0049 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0078 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0079 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0076 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0077 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_043)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_045)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0053 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0053 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [(alpha_dummy_058, alpha_dummy_061), (alpha_dummy_057, alpha_dummy_060), (alpha_dummy_056, alpha_dummy_059), (alpha_dummy_054, alpha_dummy_055), (alpha_dummy_050, alpha_dummy_052), (alpha_dummy_051, alpha_dummy_053), (alpha_dummy_076, alpha_dummy_077), (alpha_dummy_074, alpha_dummy_075), (alpha_dummy_043, alpha_dummy_045), (alpha_dummy_042, alpha_dummy_044), (alpha_dummy_072, alpha_dummy_073), (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_c1c) wpp_refl_0010)) (TAlphaWff.neg (TAlphaWff.neg split_alpha_0007))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [(alpha_dummy_054, alpha_dummy_055), (alpha_dummy_050, alpha_dummy_052), (alpha_dummy_051, alpha_dummy_053), (alpha_dummy_076, alpha_dummy_077), (alpha_dummy_074, alpha_dummy_075), (alpha_dummy_043, alpha_dummy_045), (alpha_dummy_042, alpha_dummy_044), (alpha_dummy_072, alpha_dummy_073), (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_cnnc) wpp_refl_0012)))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [(alpha_dummy_054, alpha_dummy_055), (alpha_dummy_050, alpha_dummy_052), (alpha_dummy_051, alpha_dummy_053), (alpha_dummy_076, alpha_dummy_077), (alpha_dummy_074, alpha_dummy_075), (alpha_dummy_043, alpha_dummy_045), (alpha_dummy_042, alpha_dummy_044), (alpha_dummy_072, alpha_dummy_073), (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_cnnc) wpp_refl_0012))))))))))))))
  have wpp_notmem_0190 : alpha_dummy_003 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0191 : z ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0192 : alpha_dummy_000 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0193 : w ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0194 : alpha_dummy_046 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0195 : alpha_dummy_047 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0196 : alpha_dummy_072 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0197 : alpha_dummy_073 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0198 : alpha_dummy_042 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0199 : alpha_dummy_044 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0200 : alpha_dummy_043 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0201 : alpha_dummy_045 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0202 : alpha_dummy_074 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0203 : alpha_dummy_075 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_refl_0013 : TReflOn [(alpha_dummy_074, alpha_dummy_075), (alpha_dummy_043, alpha_dummy_045), (alpha_dummy_042, alpha_dummy_044), (alpha_dummy_072, alpha_dummy_073), (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    intro u hu
    exact (TAlphaVar.there (fun h_eq => (wpp_notmem_0202) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0203) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0200) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0201) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0198) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0199) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0196) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0197) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0194) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0195) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0192) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0193) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0190) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0191) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0094) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0095) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0092) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0093) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0090) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0091) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp))))))))))))
  have split_alpha_0009 : TAlphaWff [(alpha_dummy_046, alpha_dummy_047), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (Wff.imp (Wff.classMem (Class.cv alpha_dummy_046) (syn_ccompl (Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cphi (Class.cv alpha_dummy_043))))))) (Wff.neg (Wff.classMem (Class.cv alpha_dummy_046) (syn_ccompl (Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_000) (Wff.classEq (Class.cv alpha_dummy_042) (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c)))))))))) (Wff.imp (Wff.classMem (Class.cv alpha_dummy_047) (syn_ccompl (Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cphi (Class.cv alpha_dummy_045))))))) (Wff.neg (Wff.classMem (Class.cv alpha_dummy_047) (syn_ccompl (Class.cab alpha_dummy_044 (syn_wrex alpha_dummy_045 (Class.cv w) (Wff.classEq (Class.cv alpha_dummy_044) (syn_cun (syn_cphi (Class.cv alpha_dummy_045)) (syn_csn (syn_c0c)))))))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg split_alpha_0006)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg split_alpha_0006)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0072 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0072 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0074 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0075 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0071 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0073 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_003)).fv ∪ ((Class.cv alpha_dummy_000)).fv) (by decide)) (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv w)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg split_alpha_0008))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg split_alpha_0008))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [(alpha_dummy_074, alpha_dummy_075), (alpha_dummy_043, alpha_dummy_045), (alpha_dummy_042, alpha_dummy_044), (alpha_dummy_072, alpha_dummy_073), (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_ccompl (syn_csn (syn_c0c))) wpp_refl_0013)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0072 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0072 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0074 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0075 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0071 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0073 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_003)).fv ∪ ((Class.cv alpha_dummy_000)).fv) (by decide)) (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv w)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg split_alpha_0008))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg split_alpha_0008))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [(alpha_dummy_074, alpha_dummy_075), (alpha_dummy_043, alpha_dummy_045), (alpha_dummy_042, alpha_dummy_044), (alpha_dummy_072, alpha_dummy_073), (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_ccompl (syn_csn (syn_c0c))) wpp_refl_0013))))))))))))))))))))))))
  have wpp_notmem_0204 : alpha_dummy_082 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0205 : alpha_dummy_083 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0206 : alpha_dummy_084 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0207 : alpha_dummy_085 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0208 : alpha_dummy_078 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0209 : alpha_dummy_080 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0210 : alpha_dummy_079 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0211 : alpha_dummy_081 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0212 : alpha_dummy_087 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0213 : alpha_dummy_089 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0214 : alpha_dummy_086 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0215 : alpha_dummy_088 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0216 : alpha_dummy_090 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0217 : alpha_dummy_091 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0218 : alpha_dummy_092 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0219 : alpha_dummy_095 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0220 : alpha_dummy_093 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0221 : alpha_dummy_096 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0222 : alpha_dummy_094 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0223 : alpha_dummy_097 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0014 : TReflOn [(alpha_dummy_094, alpha_dummy_097), (alpha_dummy_093, alpha_dummy_096), (alpha_dummy_092, alpha_dummy_095), (alpha_dummy_090, alpha_dummy_091), (alpha_dummy_086, alpha_dummy_088), (alpha_dummy_087, alpha_dummy_089), (alpha_dummy_079, alpha_dummy_081), (alpha_dummy_078, alpha_dummy_080), (alpha_dummy_084, alpha_dummy_085), (alpha_dummy_082, alpha_dummy_083), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] ((syn_c1c)).fv := by
    intro u hu
    exact (TAlphaVar.there (fun h_eq => (wpp_notmem_0222) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0223) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0220) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0221) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0218) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0219) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0216) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0217) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0214) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0215) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0212) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0213) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0210) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0211) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0208) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0209) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0206) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0207) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0204) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0205) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0108) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0109) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0106) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0107) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0004) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0005) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0002) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0003) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0000) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0001) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp)))))))))))))))))
  have wpp_notmem_0224 : alpha_dummy_082 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0225 : alpha_dummy_083 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0226 : alpha_dummy_084 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0227 : alpha_dummy_085 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0228 : alpha_dummy_078 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0229 : alpha_dummy_080 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0230 : alpha_dummy_079 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0231 : alpha_dummy_081 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0232 : alpha_dummy_087 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0233 : alpha_dummy_089 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0234 : alpha_dummy_086 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0235 : alpha_dummy_088 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0236 : alpha_dummy_090 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0237 : alpha_dummy_091 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0238 : alpha_dummy_092 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0239 : alpha_dummy_095 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0240 : alpha_dummy_093 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0241 : alpha_dummy_096 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0242 : alpha_dummy_094 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0243 : alpha_dummy_097 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0015 : TReflOn [(alpha_dummy_094, alpha_dummy_097), (alpha_dummy_093, alpha_dummy_096), (alpha_dummy_092, alpha_dummy_095), (alpha_dummy_090, alpha_dummy_091), (alpha_dummy_086, alpha_dummy_088), (alpha_dummy_087, alpha_dummy_089), (alpha_dummy_079, alpha_dummy_081), (alpha_dummy_078, alpha_dummy_080), (alpha_dummy_084, alpha_dummy_085), (alpha_dummy_082, alpha_dummy_083), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] ((syn_c0)).fv := by
    intro u hu
    exact (TAlphaVar.there (fun h_eq => (wpp_notmem_0242) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0243) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0240) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0241) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0238) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0239) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0236) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0237) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0234) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0235) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0232) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0233) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0230) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0231) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0228) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0229) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0226) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0227) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0224) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0225) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0132) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0133) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0130) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0131) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0030) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0031) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0028) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0029) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0026) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0027) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp)))))))))))))))))
  have split_alpha_0010 : TAlphaWff [(alpha_dummy_094, alpha_dummy_097), (alpha_dummy_093, alpha_dummy_096), (alpha_dummy_092, alpha_dummy_095), (alpha_dummy_090, alpha_dummy_091), (alpha_dummy_086, alpha_dummy_088), (alpha_dummy_087, alpha_dummy_089), (alpha_dummy_079, alpha_dummy_081), (alpha_dummy_078, alpha_dummy_080), (alpha_dummy_084, alpha_dummy_085), (alpha_dummy_082, alpha_dummy_083), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_093) (Class.cv alpha_dummy_094)) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_092) (syn_cun (Class.cv alpha_dummy_093) (Class.cv alpha_dummy_094))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_096) (Class.cv alpha_dummy_097)) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_095) (syn_cun (Class.cv alpha_dummy_096) (Class.cv alpha_dummy_097))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0094 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0095 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0092 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0093 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0098 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0099 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0096 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0097 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0094 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0095 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0092 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0093 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0098 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0099 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0096 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0097 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [(alpha_dummy_094, alpha_dummy_097), (alpha_dummy_093, alpha_dummy_096), (alpha_dummy_092, alpha_dummy_095), (alpha_dummy_090, alpha_dummy_091), (alpha_dummy_086, alpha_dummy_088), (alpha_dummy_087, alpha_dummy_089), (alpha_dummy_079, alpha_dummy_081), (alpha_dummy_078, alpha_dummy_080), (alpha_dummy_084, alpha_dummy_085), (alpha_dummy_082, alpha_dummy_083), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_c0) wpp_refl_0015)) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0102 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0103 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0100 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0101 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0102 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0103 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0100 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0101 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0106 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0107 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0104 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0105 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0106 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0107 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0104 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0105 0)) (TAlphaVar.here _ _ _)))))))))))))))))))
  have wpp_notmem_0244 : alpha_dummy_082 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0245 : alpha_dummy_083 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0246 : alpha_dummy_084 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0247 : alpha_dummy_085 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0248 : alpha_dummy_078 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0249 : alpha_dummy_080 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0250 : alpha_dummy_079 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0251 : alpha_dummy_081 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0252 : alpha_dummy_087 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0253 : alpha_dummy_089 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0254 : alpha_dummy_086 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0255 : alpha_dummy_088 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0256 : alpha_dummy_090 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0257 : alpha_dummy_091 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0016 : TReflOn [(alpha_dummy_090, alpha_dummy_091), (alpha_dummy_086, alpha_dummy_088), (alpha_dummy_087, alpha_dummy_089), (alpha_dummy_079, alpha_dummy_081), (alpha_dummy_078, alpha_dummy_080), (alpha_dummy_084, alpha_dummy_085), (alpha_dummy_082, alpha_dummy_083), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] ((syn_cnnc)).fv := by
    intro u hu
    exact (TAlphaVar.there (fun h_eq => (wpp_notmem_0256) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0257) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0254) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0255) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0252) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0253) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0250) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0251) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0248) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0249) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0246) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0247) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0244) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0245) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0156) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0157) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0154) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0155) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0056) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0057) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0054) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0055) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0052) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0053) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp))))))))))))))
  have split_alpha_0011 : TAlphaWff [(alpha_dummy_079, alpha_dummy_081), (alpha_dummy_078, alpha_dummy_080), (alpha_dummy_084, alpha_dummy_085), (alpha_dummy_082, alpha_dummy_083), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (Wff.imp (Wff.classMem (Class.cv alpha_dummy_079) (Class.cv alpha_dummy_000)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_078) (syn_cphi (Class.cv alpha_dummy_079))))) (Wff.imp (Wff.classMem (Class.cv alpha_dummy_081) (Class.cv w)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_080) (syn_cphi (Class.cv alpha_dummy_081))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0080 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0082 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0080 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0082 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0084 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0085 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0081 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0083 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_003)).fv) (by decide)) (freshVar_injective (((Class.cv w)).fv ∪ ((Class.cv z)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0086 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0087 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0086 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0087 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_079)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_081)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0090 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0091 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0090 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0091 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0088 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0089 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [(alpha_dummy_094, alpha_dummy_097), (alpha_dummy_093, alpha_dummy_096), (alpha_dummy_092, alpha_dummy_095), (alpha_dummy_090, alpha_dummy_091), (alpha_dummy_086, alpha_dummy_088), (alpha_dummy_087, alpha_dummy_089), (alpha_dummy_079, alpha_dummy_081), (alpha_dummy_078, alpha_dummy_080), (alpha_dummy_084, alpha_dummy_085), (alpha_dummy_082, alpha_dummy_083), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_c1c) wpp_refl_0014)) (TAlphaWff.neg (TAlphaWff.neg split_alpha_0010))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0088 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0089 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [(alpha_dummy_090, alpha_dummy_091), (alpha_dummy_086, alpha_dummy_088), (alpha_dummy_087, alpha_dummy_089), (alpha_dummy_079, alpha_dummy_081), (alpha_dummy_078, alpha_dummy_080), (alpha_dummy_084, alpha_dummy_085), (alpha_dummy_082, alpha_dummy_083), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_cnnc) wpp_refl_0016)))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0088 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0089 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0088 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0089 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [(alpha_dummy_090, alpha_dummy_091), (alpha_dummy_086, alpha_dummy_088), (alpha_dummy_087, alpha_dummy_089), (alpha_dummy_079, alpha_dummy_081), (alpha_dummy_078, alpha_dummy_080), (alpha_dummy_084, alpha_dummy_085), (alpha_dummy_082, alpha_dummy_083), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_cnnc) wpp_refl_0016)))))))))))))))))))
  have wpp_notmem_0258 : alpha_dummy_108 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0259 : alpha_dummy_109 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0260 : alpha_dummy_110 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0261 : alpha_dummy_111 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0262 : alpha_dummy_112 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0263 : alpha_dummy_113 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0017 : TReflOn [(alpha_dummy_094, alpha_dummy_097), (alpha_dummy_093, alpha_dummy_096), (alpha_dummy_092, alpha_dummy_095), (alpha_dummy_090, alpha_dummy_091), (alpha_dummy_086, alpha_dummy_088), (alpha_dummy_087, alpha_dummy_089), (alpha_dummy_112, alpha_dummy_113), (alpha_dummy_110, alpha_dummy_111), (alpha_dummy_079, alpha_dummy_081), (alpha_dummy_078, alpha_dummy_080), (alpha_dummy_108, alpha_dummy_109), (alpha_dummy_082, alpha_dummy_083), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] ((syn_c1c)).fv := by
    intro u hu
    exact (TAlphaVar.there (fun h_eq => (wpp_notmem_0222) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0223) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0220) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0221) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0218) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0219) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0216) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0217) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0214) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0215) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0212) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0213) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0262) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0263) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0260) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0261) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0210) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0211) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0208) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0209) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0258) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0259) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0204) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0205) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0108) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0109) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0106) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0107) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0004) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0005) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0002) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0003) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0000) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0001) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp)))))))))))))))))))
  have wpp_notmem_0264 : alpha_dummy_108 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0265 : alpha_dummy_109 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0266 : alpha_dummy_110 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0267 : alpha_dummy_111 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0268 : alpha_dummy_112 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0269 : alpha_dummy_113 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0018 : TReflOn [(alpha_dummy_094, alpha_dummy_097), (alpha_dummy_093, alpha_dummy_096), (alpha_dummy_092, alpha_dummy_095), (alpha_dummy_090, alpha_dummy_091), (alpha_dummy_086, alpha_dummy_088), (alpha_dummy_087, alpha_dummy_089), (alpha_dummy_112, alpha_dummy_113), (alpha_dummy_110, alpha_dummy_111), (alpha_dummy_079, alpha_dummy_081), (alpha_dummy_078, alpha_dummy_080), (alpha_dummy_108, alpha_dummy_109), (alpha_dummy_082, alpha_dummy_083), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] ((syn_c0)).fv := by
    intro u hu
    exact (TAlphaVar.there (fun h_eq => (wpp_notmem_0242) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0243) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0240) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0241) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0238) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0239) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0236) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0237) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0234) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0235) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0232) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0233) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0268) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0269) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0266) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0267) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0230) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0231) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0228) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0229) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0264) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0265) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0224) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0225) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0132) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0133) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0130) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0131) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0030) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0031) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0028) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0029) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0026) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0027) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp)))))))))))))))))))
  have split_alpha_0012 : TAlphaWff [(alpha_dummy_094, alpha_dummy_097), (alpha_dummy_093, alpha_dummy_096), (alpha_dummy_092, alpha_dummy_095), (alpha_dummy_090, alpha_dummy_091), (alpha_dummy_086, alpha_dummy_088), (alpha_dummy_087, alpha_dummy_089), (alpha_dummy_112, alpha_dummy_113), (alpha_dummy_110, alpha_dummy_111), (alpha_dummy_079, alpha_dummy_081), (alpha_dummy_078, alpha_dummy_080), (alpha_dummy_108, alpha_dummy_109), (alpha_dummy_082, alpha_dummy_083), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_093) (Class.cv alpha_dummy_094)) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_092) (syn_cun (Class.cv alpha_dummy_093) (Class.cv alpha_dummy_094))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_096) (Class.cv alpha_dummy_097)) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_095) (syn_cun (Class.cv alpha_dummy_096) (Class.cv alpha_dummy_097))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0094 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0095 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0092 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0093 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0098 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0099 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0096 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0097 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0094 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0095 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0092 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0093 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0098 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0099 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0096 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0097 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [(alpha_dummy_094, alpha_dummy_097), (alpha_dummy_093, alpha_dummy_096), (alpha_dummy_092, alpha_dummy_095), (alpha_dummy_090, alpha_dummy_091), (alpha_dummy_086, alpha_dummy_088), (alpha_dummy_087, alpha_dummy_089), (alpha_dummy_112, alpha_dummy_113), (alpha_dummy_110, alpha_dummy_111), (alpha_dummy_079, alpha_dummy_081), (alpha_dummy_078, alpha_dummy_080), (alpha_dummy_108, alpha_dummy_109), (alpha_dummy_082, alpha_dummy_083), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_c0) wpp_refl_0018)) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0102 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0103 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0100 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0101 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0102 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0103 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0100 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0101 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_088)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0106 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0107 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0104 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0105 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0106 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0107 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0104 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0105 0)) (TAlphaVar.here _ _ _)))))))))))))))))))
  have wpp_notmem_0270 : alpha_dummy_108 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0271 : alpha_dummy_109 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0272 : alpha_dummy_110 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0273 : alpha_dummy_111 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0274 : alpha_dummy_112 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0275 : alpha_dummy_113 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0019 : TReflOn [(alpha_dummy_090, alpha_dummy_091), (alpha_dummy_086, alpha_dummy_088), (alpha_dummy_087, alpha_dummy_089), (alpha_dummy_112, alpha_dummy_113), (alpha_dummy_110, alpha_dummy_111), (alpha_dummy_079, alpha_dummy_081), (alpha_dummy_078, alpha_dummy_080), (alpha_dummy_108, alpha_dummy_109), (alpha_dummy_082, alpha_dummy_083), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] ((syn_cnnc)).fv := by
    intro u hu
    exact (TAlphaVar.there (fun h_eq => (wpp_notmem_0256) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0257) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0254) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0255) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0252) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0253) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0274) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0275) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0272) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0273) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0250) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0251) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0248) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0249) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0270) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0271) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0244) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0245) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0156) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0157) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0154) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0155) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0056) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0057) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0054) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0055) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0052) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0053) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp))))))))))))))))
  have split_alpha_0013 : TAlphaWff [(alpha_dummy_087, alpha_dummy_089), (alpha_dummy_112, alpha_dummy_113), (alpha_dummy_110, alpha_dummy_111), (alpha_dummy_079, alpha_dummy_081), (alpha_dummy_078, alpha_dummy_080), (alpha_dummy_108, alpha_dummy_109), (alpha_dummy_082, alpha_dummy_083), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (Wff.all alpha_dummy_086 (Wff.neg (syn_wa (Wff.classMem (Class.cv alpha_dummy_086) (Class.cv alpha_dummy_079)) (Wff.classEq (Class.cv alpha_dummy_087) (syn_cif (Wff.classMem (Class.cv alpha_dummy_086) (syn_cnnc)) (syn_cplc (Class.cv alpha_dummy_086) (syn_c1c)) (Class.cv alpha_dummy_086)))))) (Wff.all alpha_dummy_088 (Wff.neg (syn_wa (Wff.classMem (Class.cv alpha_dummy_088) (Class.cv alpha_dummy_081)) (Wff.classEq (Class.cv alpha_dummy_089) (syn_cif (Wff.classMem (Class.cv alpha_dummy_088) (syn_cnnc)) (syn_cplc (Class.cv alpha_dummy_088) (syn_c1c)) (Class.cv alpha_dummy_088)))))) :=
    (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0086 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0087 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0086 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0087 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0116 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0117 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0114 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0115 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_079)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_081)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0090 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0091 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0090 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0091 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0088 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0089 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [(alpha_dummy_094, alpha_dummy_097), (alpha_dummy_093, alpha_dummy_096), (alpha_dummy_092, alpha_dummy_095), (alpha_dummy_090, alpha_dummy_091), (alpha_dummy_086, alpha_dummy_088), (alpha_dummy_087, alpha_dummy_089), (alpha_dummy_112, alpha_dummy_113), (alpha_dummy_110, alpha_dummy_111), (alpha_dummy_079, alpha_dummy_081), (alpha_dummy_078, alpha_dummy_080), (alpha_dummy_108, alpha_dummy_109), (alpha_dummy_082, alpha_dummy_083), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_c1c) wpp_refl_0017)) (TAlphaWff.neg (TAlphaWff.neg split_alpha_0012))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0088 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0089 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [(alpha_dummy_090, alpha_dummy_091), (alpha_dummy_086, alpha_dummy_088), (alpha_dummy_087, alpha_dummy_089), (alpha_dummy_112, alpha_dummy_113), (alpha_dummy_110, alpha_dummy_111), (alpha_dummy_079, alpha_dummy_081), (alpha_dummy_078, alpha_dummy_080), (alpha_dummy_108, alpha_dummy_109), (alpha_dummy_082, alpha_dummy_083), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_cnnc) wpp_refl_0019)))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0088 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0089 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0088 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0089 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [(alpha_dummy_090, alpha_dummy_091), (alpha_dummy_086, alpha_dummy_088), (alpha_dummy_087, alpha_dummy_089), (alpha_dummy_112, alpha_dummy_113), (alpha_dummy_110, alpha_dummy_111), (alpha_dummy_079, alpha_dummy_081), (alpha_dummy_078, alpha_dummy_080), (alpha_dummy_108, alpha_dummy_109), (alpha_dummy_082, alpha_dummy_083), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_cnnc) wpp_refl_0019))))))))))))))
  have wpp_notmem_0276 : alpha_dummy_082 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0277 : alpha_dummy_083 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0278 : alpha_dummy_108 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0279 : alpha_dummy_109 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0280 : alpha_dummy_078 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0281 : alpha_dummy_080 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0282 : alpha_dummy_079 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0283 : alpha_dummy_081 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0284 : alpha_dummy_110 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0285 : alpha_dummy_111 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact (fun h_mem => ((fun h_mem => ((fun h_mem => ((fun h_mem => (by simpa using h_mem))) ((fv_syn_c0c) ▸ h_mem))) ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_refl_0020 : TReflOn [(alpha_dummy_110, alpha_dummy_111), (alpha_dummy_079, alpha_dummy_081), (alpha_dummy_078, alpha_dummy_080), (alpha_dummy_108, alpha_dummy_109), (alpha_dummy_082, alpha_dummy_083), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    intro u hu
    exact (TAlphaVar.there (fun h_eq => (wpp_notmem_0284) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0285) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0282) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0283) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0280) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0281) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0278) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0279) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0276) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0277) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0192) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0193) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0190) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0191) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0094) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0095) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0092) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0093) (h_eq ▸ hu)) (TAlphaVar.there (fun h_eq => (wpp_notmem_0090) (h_eq ▸ hu)) (fun h_eq => (wpp_notmem_0091) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp))))))))))))
  have split_alpha_0014 : TAlphaWff [(alpha_dummy_082, alpha_dummy_083), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (Wff.classMem (Class.cv alpha_dummy_082) (syn_ccompl (Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_003) (Wff.classEq (Class.cv alpha_dummy_078) (syn_cun (syn_cphi (Class.cv alpha_dummy_079)) (syn_csn (syn_c0c)))))))) (Wff.classMem (Class.cv alpha_dummy_083) (syn_ccompl (Class.cab alpha_dummy_080 (syn_wrex alpha_dummy_081 (Class.cv z) (Wff.classEq (Class.cv alpha_dummy_080) (syn_cun (syn_cphi (Class.cv alpha_dummy_081)) (syn_csn (syn_c0c)))))))) :=
    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0108 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0110 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0108 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0110 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0112 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0113 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0109 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0111 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) (Ne.symm dv_w_z) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_003)).fv) (by decide)) (freshVar_injective (((Class.cv w)).fv ∪ ((Class.cv z)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg split_alpha_0013))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg split_alpha_0013))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [(alpha_dummy_110, alpha_dummy_111), (alpha_dummy_079, alpha_dummy_081), (alpha_dummy_078, alpha_dummy_080), (alpha_dummy_108, alpha_dummy_109), (alpha_dummy_082, alpha_dummy_083), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_ccompl (syn_csn (syn_c0c))) wpp_refl_0020)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0108 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0110 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0108 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0110 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0112 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0113 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0109 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0111 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) (Ne.symm dv_w_z) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_003)).fv) (by decide)) (freshVar_injective (((Class.cv w)).fv ∪ ((Class.cv z)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg split_alpha_0013))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg split_alpha_0013))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [(alpha_dummy_110, alpha_dummy_111), (alpha_dummy_079, alpha_dummy_081), (alpha_dummy_078, alpha_dummy_080), (alpha_dummy_108, alpha_dummy_109), (alpha_dummy_082, alpha_dummy_083), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x), (alpha_dummy_004, alpha_dummy_005)] (syn_ccompl (syn_csn (syn_c0c))) wpp_refl_0020))))))))))))))))))))))
  exact Nominal.alphaClassEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp split_alpha_0004 (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) (Ne.symm dv_w_x) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_z (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg split_alpha_0009)))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) (Ne.symm dv_w_y) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg split_alpha_0011)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg split_alpha_0011)))))))))))) (TAlphaWff.neg split_alpha_0014)))))))))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
