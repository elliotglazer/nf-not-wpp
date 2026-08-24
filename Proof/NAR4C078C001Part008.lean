import NAR4C078C001Part007

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

noncomputable def nb078_alpha_dummy_1050 : Var := (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv) 1)

noncomputable def nb078_alpha_dummy_1051 : Var := (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv) 2)

noncomputable def nb078_alpha_dummy_1052 (h : Var) : Var := (freshVar (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) 0)

noncomputable def nb078_alpha_dummy_1053 (h : Var) : Var := (freshVar (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) 1)

noncomputable def nb078_alpha_dummy_1054 (h : Var) : Var := (freshVar (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) 2)

noncomputable def nb078_alpha_dummy_1055 : Var := (freshVar (({(nb078_alpha_dummy_1049)} : Finset Var) ∪ ({(nb078_alpha_dummy_1050)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_1051) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_1049)) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))) (Class.cv (nb078_alpha_dummy_1051))) (syn_wbr (Class.cv (nb078_alpha_dummy_1051)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_1050)))))).fv) 0)

noncomputable def nb078_alpha_dummy_1056 (h : Var) : Var := (freshVar (({(nb078_alpha_dummy_1052 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_1053 h)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_1054 h) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_1052 h)) (syn_ccnv (syn_ccnv (Class.cv h))) (Class.cv (nb078_alpha_dummy_1054 h))) (syn_wbr (Class.cv (nb078_alpha_dummy_1054 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb078_alpha_dummy_1053 h)))))).fv) 0)

noncomputable def nb078_alpha_dummy_1057 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) 0)

noncomputable def nb078_alpha_dummy_1058 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) 1)

noncomputable def nb078_alpha_dummy_1059 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1053 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1060 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1053 h))).fv) 1)

noncomputable def nb078_alpha_dummy_1061 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_1057) (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1057)) (syn_cphi (Class.cv (nb078_alpha_dummy_1058)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1057) (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1050)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1057)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1058))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1062 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_1059 h) (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1059 h) (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1053 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1063 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_1057) (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1057)) (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1057) (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1057)) (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1064 (h : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_1059 h) (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1059 h) (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1065 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1058))).fv) 0)

noncomputable def nb078_alpha_dummy_1066 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1058))).fv) 1)

noncomputable def nb078_alpha_dummy_1067 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1060 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1068 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1060 h))).fv) 1)

noncomputable def nb078_alpha_dummy_1069 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_1065)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1065)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1065))).fv) 0)

noncomputable def nb078_alpha_dummy_1070 (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_1067 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1067 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1067 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1071 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_1072 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_1073 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_1074 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_1075 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_1076 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_1077 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_1072)) (Class.cv (nb078_alpha_dummy_1073)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1072)) (Class.cv (nb078_alpha_dummy_1073)))).fv) 0)

noncomputable def nb078_alpha_dummy_1078 (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_1075 h)) (Class.cv (nb078_alpha_dummy_1076 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1075 h)) (Class.cv (nb078_alpha_dummy_1076 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_1079 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1072))).fv ∪ ((Class.cv (nb078_alpha_dummy_1073))).fv) 0)

noncomputable def nb078_alpha_dummy_1080 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1075 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1076 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1081 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_1072)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_1073)))).fv) 0)

noncomputable def nb078_alpha_dummy_1082 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_1075 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_1076 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_1083 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1072))).fv ∪ ((Class.cv (nb078_alpha_dummy_1072))).fv) 0)

noncomputable def nb078_alpha_dummy_1084 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1075 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1075 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1085 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1073))).fv ∪ ((Class.cv (nb078_alpha_dummy_1073))).fv) 0)

noncomputable def nb078_alpha_dummy_1086 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1076 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1076 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1087 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_1057) (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1050)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1057)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1058))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1057) (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1050)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1057)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1058))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1088 (h : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_1059 h) (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1053 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1059 h) (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1053 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1089 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_1090 (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_1091 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_1058)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1058)))).fv) 0)

noncomputable def nb078_alpha_dummy_1092 (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_1093 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1051))).fv) 0)

noncomputable def nb078_alpha_dummy_1094 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1051))).fv) 1)

noncomputable def nb078_alpha_dummy_1095 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1054 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1096 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1054 h))).fv) 1)

noncomputable def nb078_alpha_dummy_1097 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_1093) (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1049)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1093)) (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1093) (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1051)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1093)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1094))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1098 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_1095 h) (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1052 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1095 h) (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1054 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1099 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_1093) (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1049)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1093)) (syn_cphi (Class.cv (nb078_alpha_dummy_1094))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1093) (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1049)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1093)) (syn_cphi (Class.cv (nb078_alpha_dummy_1094))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1100 (h : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_1095 h) (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1052 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1095 h) (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1052 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1101 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1094))).fv) 0)

noncomputable def nb078_alpha_dummy_1102 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1094))).fv) 1)

noncomputable def nb078_alpha_dummy_1103 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1096 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1104 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1096 h))).fv) 1)

noncomputable def nb078_alpha_dummy_1105 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_1101)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1101)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1101))).fv) 0)

noncomputable def nb078_alpha_dummy_1106 (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_1103 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1103 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1103 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1107 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_1108 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_1109 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_1110 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_1111 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_1112 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_1113 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_1108)) (Class.cv (nb078_alpha_dummy_1109)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1108)) (Class.cv (nb078_alpha_dummy_1109)))).fv) 0)

noncomputable def nb078_alpha_dummy_1114 (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_1111 h)) (Class.cv (nb078_alpha_dummy_1112 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1111 h)) (Class.cv (nb078_alpha_dummy_1112 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_1115 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1108))).fv ∪ ((Class.cv (nb078_alpha_dummy_1109))).fv) 0)

noncomputable def nb078_alpha_dummy_1116 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1111 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1112 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1117 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_1108)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_1109)))).fv) 0)

noncomputable def nb078_alpha_dummy_1118 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_1111 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_1112 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_1119 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1108))).fv ∪ ((Class.cv (nb078_alpha_dummy_1108))).fv) 0)

noncomputable def nb078_alpha_dummy_1120 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1111 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1111 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1121 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1109))).fv ∪ ((Class.cv (nb078_alpha_dummy_1109))).fv) 0)

noncomputable def nb078_alpha_dummy_1122 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1112 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1112 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1123 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_1093) (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1051)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1093)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1094))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1093) (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1051)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1093)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1094))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1124 (h : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_1095 h) (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1054 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1095 h) (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1054 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1125 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1094))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_1126 (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_1127 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_1094)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1094)))).fv) 0)

noncomputable def nb078_alpha_dummy_1128 (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_1129 : Var := (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) 0)

noncomputable def nb078_alpha_dummy_1130 : Var := (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) 1)

noncomputable def nb078_alpha_dummy_1131 (h : Var) : Var := (freshVar (((syn_ccnv (Class.cv h))).fv) 0)

noncomputable def nb078_alpha_dummy_1132 (h : Var) : Var := (freshVar (((syn_ccnv (Class.cv h))).fv) 1)

noncomputable def nb078_alpha_dummy_1133 : Var := (freshVar (({(nb078_alpha_dummy_1129)} : Finset Var) ∪ ({(nb078_alpha_dummy_1130)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_1130)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_1129)))).fv) 0)

noncomputable def nb078_alpha_dummy_1134 (h : Var) : Var := (freshVar (({(nb078_alpha_dummy_1131 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_1132 h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_1132 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb078_alpha_dummy_1131 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_1135 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1129))).fv ∪ ((Class.cv (nb078_alpha_dummy_1130))).fv) 0)

noncomputable def nb078_alpha_dummy_1136 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1129))).fv ∪ ((Class.cv (nb078_alpha_dummy_1130))).fv) 1)

noncomputable def nb078_alpha_dummy_1137 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1131 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1132 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1138 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1131 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1132 h))).fv) 1)

noncomputable def nb078_alpha_dummy_1139 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_1135) (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1129)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1135)) (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1135) (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1130)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1135)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1136))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1140 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_1137 h) (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1131 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1137 h) (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1132 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1141 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_1135) (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1129)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1135)) (syn_cphi (Class.cv (nb078_alpha_dummy_1136))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1135) (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1129)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1135)) (syn_cphi (Class.cv (nb078_alpha_dummy_1136))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1142 (h : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_1137 h) (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1131 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1137 h) (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1131 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1143 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1136))).fv) 0)

noncomputable def nb078_alpha_dummy_1144 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1136))).fv) 1)

noncomputable def nb078_alpha_dummy_1145 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1138 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1146 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1138 h))).fv) 1)

noncomputable def nb078_alpha_dummy_1147 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_1143)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1143)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1143))).fv) 0)

noncomputable def nb078_alpha_dummy_1148 (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_1145 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1145 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1145 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1149 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_1150 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_1151 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_1152 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_1153 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_1154 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_1155 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_1150)) (Class.cv (nb078_alpha_dummy_1151)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1150)) (Class.cv (nb078_alpha_dummy_1151)))).fv) 0)

noncomputable def nb078_alpha_dummy_1156 (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_1153 h)) (Class.cv (nb078_alpha_dummy_1154 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1153 h)) (Class.cv (nb078_alpha_dummy_1154 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_1157 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1150))).fv ∪ ((Class.cv (nb078_alpha_dummy_1151))).fv) 0)

noncomputable def nb078_alpha_dummy_1158 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1153 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1154 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1159 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_1150)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_1151)))).fv) 0)

noncomputable def nb078_alpha_dummy_1160 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_1153 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_1154 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_1161 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1150))).fv ∪ ((Class.cv (nb078_alpha_dummy_1150))).fv) 0)

noncomputable def nb078_alpha_dummy_1162 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1153 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1153 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1163 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1151))).fv ∪ ((Class.cv (nb078_alpha_dummy_1151))).fv) 0)

noncomputable def nb078_alpha_dummy_1164 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1154 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1154 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1165 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_1135) (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1130)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1135)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1136))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1135) (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1130)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1135)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1136))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1166 (h : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_1137 h) (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1132 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1137 h) (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1132 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1167 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1136))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_1168 (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_1169 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_1136)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1136)))).fv) 0)

noncomputable def nb078_alpha_dummy_1170 (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_1171 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1130))).fv ∪ ((Class.cv (nb078_alpha_dummy_1129))).fv) 0)

noncomputable def nb078_alpha_dummy_1172 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1130))).fv ∪ ((Class.cv (nb078_alpha_dummy_1129))).fv) 1)

noncomputable def nb078_alpha_dummy_1173 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1132 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1131 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1174 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1132 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1131 h))).fv) 1)

noncomputable def nb078_alpha_dummy_1175 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_1171) (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1130)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1171)) (syn_cphi (Class.cv (nb078_alpha_dummy_1172)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1171) (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1129)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1171)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1172))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1176 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_1173 h) (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1132 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1173 h) (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1131 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1177 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_1171) (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1130)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1171)) (syn_cphi (Class.cv (nb078_alpha_dummy_1172))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1171) (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1130)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1171)) (syn_cphi (Class.cv (nb078_alpha_dummy_1172))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1178 (h : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_1173 h) (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1132 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1173 h) (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1132 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1179 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1172))).fv) 0)

noncomputable def nb078_alpha_dummy_1180 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1172))).fv) 1)

noncomputable def nb078_alpha_dummy_1181 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1174 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1182 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1174 h))).fv) 1)

noncomputable def nb078_alpha_dummy_1183 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_1179)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1179)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1179))).fv) 0)

noncomputable def nb078_alpha_dummy_1184 (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_1181 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1181 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1181 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1185 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_1186 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_1187 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_1188 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_1189 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_1190 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_1191 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_1186)) (Class.cv (nb078_alpha_dummy_1187)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1186)) (Class.cv (nb078_alpha_dummy_1187)))).fv) 0)

noncomputable def nb078_alpha_dummy_1192 (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_1189 h)) (Class.cv (nb078_alpha_dummy_1190 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1189 h)) (Class.cv (nb078_alpha_dummy_1190 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_1193 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1186))).fv ∪ ((Class.cv (nb078_alpha_dummy_1187))).fv) 0)

noncomputable def nb078_alpha_dummy_1194 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1189 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1190 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1195 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_1186)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_1187)))).fv) 0)

noncomputable def nb078_alpha_dummy_1196 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_1189 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_1190 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_1197 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1186))).fv ∪ ((Class.cv (nb078_alpha_dummy_1186))).fv) 0)

noncomputable def nb078_alpha_dummy_1198 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1189 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1189 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1199 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1187))).fv ∪ ((Class.cv (nb078_alpha_dummy_1187))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
