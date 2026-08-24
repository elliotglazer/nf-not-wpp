import NAR4C078C001Part156

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

noncomputable def nb078_split_alpha_0137 (x : Var) (y : Var) (h : Var) : TAlphaWff [((nb078_alpha_dummy_1127), (nb078_alpha_dummy_1128 h)), ((nb078_alpha_dummy_1125), (nb078_alpha_dummy_1126 h)), ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)), ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)), ((nb078_alpha_dummy_1123), (nb078_alpha_dummy_1124 h)), ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1127)) (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_1127)) (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))))) (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1128 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_1128 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1144) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1145 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1144) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1145 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1174) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1175 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1172) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1173 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1094))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1096 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1148) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1149 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1148) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1149 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1147 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1109), (nb078_alpha_dummy_1112 h)), ((nb078_alpha_dummy_1108), (nb078_alpha_dummy_1111 h)), ((nb078_alpha_dummy_1107), (nb078_alpha_dummy_1110 h)), ((nb078_alpha_dummy_1105), (nb078_alpha_dummy_1106 h)), ((nb078_alpha_dummy_1101), (nb078_alpha_dummy_1103 h)), ((nb078_alpha_dummy_1102), (nb078_alpha_dummy_1104 h)), ((nb078_alpha_dummy_1127), (nb078_alpha_dummy_1128 h)), ((nb078_alpha_dummy_1125), (nb078_alpha_dummy_1126 h)), ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)), ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)), ((nb078_alpha_dummy_1123), (nb078_alpha_dummy_1124 h)), ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0456 x y h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1152) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1153 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1150) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1151 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1156) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1157 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1154) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1155 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1152) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1153 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1150) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1151 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1156) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1157 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1154) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1155 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1109), (nb078_alpha_dummy_1112 h)), ((nb078_alpha_dummy_1108), (nb078_alpha_dummy_1111 h)), ((nb078_alpha_dummy_1107), (nb078_alpha_dummy_1110 h)), ((nb078_alpha_dummy_1105), (nb078_alpha_dummy_1106 h)), ((nb078_alpha_dummy_1101), (nb078_alpha_dummy_1103 h)), ((nb078_alpha_dummy_1102), (nb078_alpha_dummy_1104 h)), ((nb078_alpha_dummy_1127), (nb078_alpha_dummy_1128 h)), ((nb078_alpha_dummy_1125), (nb078_alpha_dummy_1126 h)), ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)), ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)), ((nb078_alpha_dummy_1123), (nb078_alpha_dummy_1124 h)), ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0457 x y h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1160) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1161 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1158) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1159 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1160) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1161 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1158) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1159 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1164) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1165 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1162) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1163 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1164) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1165 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1162) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1163 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1147 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1105), (nb078_alpha_dummy_1106 h)), ((nb078_alpha_dummy_1101), (nb078_alpha_dummy_1103 h)), ((nb078_alpha_dummy_1102), (nb078_alpha_dummy_1104 h)), ((nb078_alpha_dummy_1127), (nb078_alpha_dummy_1128 h)), ((nb078_alpha_dummy_1125), (nb078_alpha_dummy_1126 h)), ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)), ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)), ((nb078_alpha_dummy_1123), (nb078_alpha_dummy_1124 h)), ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0458 x y h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1147 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1147 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1105), (nb078_alpha_dummy_1106 h)), ((nb078_alpha_dummy_1101), (nb078_alpha_dummy_1103 h)), ((nb078_alpha_dummy_1102), (nb078_alpha_dummy_1104 h)), ((nb078_alpha_dummy_1127), (nb078_alpha_dummy_1128 h)), ((nb078_alpha_dummy_1125), (nb078_alpha_dummy_1126 h)), ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)), ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)), ((nb078_alpha_dummy_1123), (nb078_alpha_dummy_1124 h)), ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0458 x y h)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1144) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1145 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1144) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1145 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1174) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1175 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1172) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1173 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1094))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1096 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1148) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1149 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1148) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1149 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1147 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1109), (nb078_alpha_dummy_1112 h)), ((nb078_alpha_dummy_1108), (nb078_alpha_dummy_1111 h)), ((nb078_alpha_dummy_1107), (nb078_alpha_dummy_1110 h)), ((nb078_alpha_dummy_1105), (nb078_alpha_dummy_1106 h)), ((nb078_alpha_dummy_1101), (nb078_alpha_dummy_1103 h)), ((nb078_alpha_dummy_1102), (nb078_alpha_dummy_1104 h)), ((nb078_alpha_dummy_1127), (nb078_alpha_dummy_1128 h)), ((nb078_alpha_dummy_1125), (nb078_alpha_dummy_1126 h)), ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)), ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)), ((nb078_alpha_dummy_1123), (nb078_alpha_dummy_1124 h)), ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0456 x y h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1152) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1153 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1150) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1151 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1156) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1157 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1154) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1155 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1152) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1153 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1150) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1151 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1156) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1157 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1154) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1155 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1109), (nb078_alpha_dummy_1112 h)), ((nb078_alpha_dummy_1108), (nb078_alpha_dummy_1111 h)), ((nb078_alpha_dummy_1107), (nb078_alpha_dummy_1110 h)), ((nb078_alpha_dummy_1105), (nb078_alpha_dummy_1106 h)), ((nb078_alpha_dummy_1101), (nb078_alpha_dummy_1103 h)), ((nb078_alpha_dummy_1102), (nb078_alpha_dummy_1104 h)), ((nb078_alpha_dummy_1127), (nb078_alpha_dummy_1128 h)), ((nb078_alpha_dummy_1125), (nb078_alpha_dummy_1126 h)), ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)), ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)), ((nb078_alpha_dummy_1123), (nb078_alpha_dummy_1124 h)), ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0457 x y h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1160) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1161 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1158) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1159 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1160) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1161 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1158) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1159 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1164) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1165 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1162) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1163 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1164) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1165 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1162) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1163 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1147 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1105), (nb078_alpha_dummy_1106 h)), ((nb078_alpha_dummy_1101), (nb078_alpha_dummy_1103 h)), ((nb078_alpha_dummy_1102), (nb078_alpha_dummy_1104 h)), ((nb078_alpha_dummy_1127), (nb078_alpha_dummy_1128 h)), ((nb078_alpha_dummy_1125), (nb078_alpha_dummy_1126 h)), ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)), ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)), ((nb078_alpha_dummy_1123), (nb078_alpha_dummy_1124 h)), ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0458 x y h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1147 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1147 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1105), (nb078_alpha_dummy_1106 h)), ((nb078_alpha_dummy_1101), (nb078_alpha_dummy_1103 h)), ((nb078_alpha_dummy_1102), (nb078_alpha_dummy_1104 h)), ((nb078_alpha_dummy_1127), (nb078_alpha_dummy_1128 h)), ((nb078_alpha_dummy_1125), (nb078_alpha_dummy_1126 h)), ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)), ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)), ((nb078_alpha_dummy_1123), (nb078_alpha_dummy_1124 h)), ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0458 x y h))))))))))))))))))))

theorem nb078_wpp_notmem_2856 : (nb078_alpha_dummy_1125) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0850)

theorem nb078_wpp_notmem_2857 (h : Var) : (nb078_alpha_dummy_1126 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0851 h)

theorem nb078_wpp_notmem_2858 : (nb078_alpha_dummy_1094) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0838)

theorem nb078_wpp_notmem_2859 (h : Var) : (nb078_alpha_dummy_1096 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0839 h)

theorem nb078_wpp_notmem_2860 : (nb078_alpha_dummy_1093) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0840)

theorem nb078_wpp_notmem_2861 (h : Var) : (nb078_alpha_dummy_1095 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0841 h)

theorem nb078_wpp_notmem_2862 : (nb078_alpha_dummy_1123) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0852)

theorem nb078_wpp_notmem_2863 (h : Var) : (nb078_alpha_dummy_1124 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0853 h)

theorem nb078_wpp_notmem_2864 : (nb078_alpha_dummy_1097) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0844)

theorem nb078_wpp_notmem_2865 (h : Var) : (nb078_alpha_dummy_1098 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0845 h)

theorem nb078_wpp_notmem_2866 : (nb078_alpha_dummy_1051) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0846)

theorem nb078_wpp_notmem_2867 (h : Var) : (nb078_alpha_dummy_1054 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0847 h)

theorem nb078_compact_envfresh_0459 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_1125), (nb078_alpha_dummy_1126 h)), ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)), ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)), ((nb078_alpha_dummy_1123), (nb078_alpha_dummy_1124 h)), ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_1125) (nb078_alpha_dummy_1126 h) (nb078_wpp_notmem_2856) (nb078_wpp_notmem_2857 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1094) (nb078_alpha_dummy_1096 h) (nb078_wpp_notmem_2858) (nb078_wpp_notmem_2859 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1093) (nb078_alpha_dummy_1095 h) (nb078_wpp_notmem_2860) (nb078_wpp_notmem_2861 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1123) (nb078_alpha_dummy_1124 h) (nb078_wpp_notmem_2862) (nb078_wpp_notmem_2863 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1097) (nb078_alpha_dummy_1098 h) (nb078_wpp_notmem_2864) (nb078_wpp_notmem_2865 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1051) (nb078_alpha_dummy_1054 h) (nb078_wpp_notmem_2866) (nb078_wpp_notmem_2867 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1050) (nb078_alpha_dummy_1053 h) (nb078_wpp_notmem_2768) (nb078_wpp_notmem_2769 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1049) (nb078_alpha_dummy_1052 h) (nb078_wpp_notmem_2770) (nb078_wpp_notmem_2771 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1055) (nb078_alpha_dummy_1056 h) (nb078_wpp_notmem_2772) (nb078_wpp_notmem_2773 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1047) (nb078_alpha_dummy_1048 h) (nb078_wpp_notmem_2774) (nb078_wpp_notmem_2775 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1045) (nb078_alpha_dummy_1046 h) (nb078_wpp_notmem_2776) (nb078_wpp_notmem_2777 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_2062) (nb078_wpp_notmem_2063 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0142) (nb078_wpp_notmem_0143 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0144) (nb078_wpp_notmem_0145 x) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))))))

noncomputable def nb078_wpp_refl_0459 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_1125), (nb078_alpha_dummy_1126 h)), ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)), ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)), ((nb078_alpha_dummy_1123), (nb078_alpha_dummy_1124 h)), ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0459 x y h)

theorem nb078_compact_fv_empty_0854 : (nb078_alpha_dummy_1151) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2868 : (nb078_alpha_dummy_1151) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0854)

theorem nb078_compact_fv_empty_0855 (h : Var) : (nb078_alpha_dummy_1154 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2869 (h : Var) : (nb078_alpha_dummy_1154 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0855 h)

theorem nb078_compact_fv_empty_0856 : (nb078_alpha_dummy_1150) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2870 : (nb078_alpha_dummy_1150) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0856)

theorem nb078_compact_fv_empty_0857 (h : Var) : (nb078_alpha_dummy_1153 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2871 (h : Var) : (nb078_alpha_dummy_1153 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0857 h)

theorem nb078_compact_fv_empty_0858 : (nb078_alpha_dummy_1149) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2872 : (nb078_alpha_dummy_1149) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0858)

theorem nb078_compact_fv_empty_0859 (h : Var) : (nb078_alpha_dummy_1152 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2873 (h : Var) : (nb078_alpha_dummy_1152 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0859 h)

theorem nb078_compact_fv_empty_0860 : (nb078_alpha_dummy_1147) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2874 : (nb078_alpha_dummy_1147) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0860)

theorem nb078_compact_fv_empty_0861 (h : Var) : (nb078_alpha_dummy_1148 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2875 (h : Var) : (nb078_alpha_dummy_1148 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0861 h)

theorem nb078_compact_fv_empty_0862 : (nb078_alpha_dummy_1143) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2876 : (nb078_alpha_dummy_1143) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0862)

theorem nb078_compact_fv_empty_0863 (h : Var) : (nb078_alpha_dummy_1145 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2877 (h : Var) : (nb078_alpha_dummy_1145 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0863 h)

theorem nb078_compact_fv_empty_0864 : (nb078_alpha_dummy_1144) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2878 : (nb078_alpha_dummy_1144) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0864)

theorem nb078_compact_fv_empty_0865 (h : Var) : (nb078_alpha_dummy_1146 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2879 (h : Var) : (nb078_alpha_dummy_1146 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0865 h)

theorem nb078_compact_fv_empty_0866 : (nb078_alpha_dummy_1136) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2880 : (nb078_alpha_dummy_1136) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0866)

theorem nb078_compact_fv_empty_0867 (h : Var) : (nb078_alpha_dummy_1138 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2881 (h : Var) : (nb078_alpha_dummy_1138 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0867 h)

theorem nb078_compact_fv_empty_0868 : (nb078_alpha_dummy_1135) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2882 : (nb078_alpha_dummy_1135) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0868)

theorem nb078_compact_fv_empty_0869 (h : Var) : (nb078_alpha_dummy_1137 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2883 (h : Var) : (nb078_alpha_dummy_1137 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0869 h)

theorem nb078_compact_fv_empty_0870 : (nb078_alpha_dummy_1141) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2884 : (nb078_alpha_dummy_1141) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0870)

theorem nb078_compact_fv_empty_0871 (h : Var) : (nb078_alpha_dummy_1142 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2885 (h : Var) : (nb078_alpha_dummy_1142 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0871 h)

theorem nb078_compact_fv_empty_0872 : (nb078_alpha_dummy_1139) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2886 : (nb078_alpha_dummy_1139) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0872)

theorem nb078_compact_fv_empty_0873 (h : Var) : (nb078_alpha_dummy_1140 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2887 (h : Var) : (nb078_alpha_dummy_1140 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0873 h)

theorem nb078_compact_fv_empty_0874 : (nb078_alpha_dummy_1130) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2888 : (nb078_alpha_dummy_1130) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0874)

theorem nb078_compact_fv_empty_0875 (h : Var) : (nb078_alpha_dummy_1132 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2889 (h : Var) : (nb078_alpha_dummy_1132 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0875 h)

theorem nb078_compact_fv_empty_0876 : (nb078_alpha_dummy_1129) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2890 : (nb078_alpha_dummy_1129) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0876)

theorem nb078_compact_fv_empty_0877 (h : Var) : (nb078_alpha_dummy_1131 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2891 (h : Var) : (nb078_alpha_dummy_1131 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0877 h)

theorem nb078_compact_fv_empty_0878 : (nb078_alpha_dummy_1133) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2892 : (nb078_alpha_dummy_1133) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0878)

theorem nb078_compact_fv_empty_0879 (h : Var) : (nb078_alpha_dummy_1134 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2893 (h : Var) : (nb078_alpha_dummy_1134 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0879 h)

theorem nb078_compact_envfresh_0460 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_1151), (nb078_alpha_dummy_1154 h)), ((nb078_alpha_dummy_1150), (nb078_alpha_dummy_1153 h)), ((nb078_alpha_dummy_1149), (nb078_alpha_dummy_1152 h)), ((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)), ((nb078_alpha_dummy_1143), (nb078_alpha_dummy_1145 h)), ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)), ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)), ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)), ((nb078_alpha_dummy_1141), (nb078_alpha_dummy_1142 h)), ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_1151) (nb078_alpha_dummy_1154 h) (nb078_wpp_notmem_2868) (nb078_wpp_notmem_2869 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1150) (nb078_alpha_dummy_1153 h) (nb078_wpp_notmem_2870) (nb078_wpp_notmem_2871 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1149) (nb078_alpha_dummy_1152 h) (nb078_wpp_notmem_2872) (nb078_wpp_notmem_2873 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1147) (nb078_alpha_dummy_1148 h) (nb078_wpp_notmem_2874) (nb078_wpp_notmem_2875 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1143) (nb078_alpha_dummy_1145 h) (nb078_wpp_notmem_2876) (nb078_wpp_notmem_2877 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1144) (nb078_alpha_dummy_1146 h) (nb078_wpp_notmem_2878) (nb078_wpp_notmem_2879 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1136) (nb078_alpha_dummy_1138 h) (nb078_wpp_notmem_2880) (nb078_wpp_notmem_2881 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1135) (nb078_alpha_dummy_1137 h) (nb078_wpp_notmem_2882) (nb078_wpp_notmem_2883 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1141) (nb078_alpha_dummy_1142 h) (nb078_wpp_notmem_2884) (nb078_wpp_notmem_2885 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1139) (nb078_alpha_dummy_1140 h) (nb078_wpp_notmem_2886) (nb078_wpp_notmem_2887 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1130) (nb078_alpha_dummy_1132 h) (nb078_wpp_notmem_2888) (nb078_wpp_notmem_2889 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1129) (nb078_alpha_dummy_1131 h) (nb078_wpp_notmem_2890) (nb078_wpp_notmem_2891 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1133) (nb078_alpha_dummy_1134 h) (nb078_wpp_notmem_2892) (nb078_wpp_notmem_2893 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1051) (nb078_alpha_dummy_1054 h) (nb078_wpp_notmem_2798) (nb078_wpp_notmem_2799 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1050) (nb078_alpha_dummy_1053 h) (nb078_wpp_notmem_2676) (nb078_wpp_notmem_2677 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1049) (nb078_alpha_dummy_1052 h) (nb078_wpp_notmem_2678) (nb078_wpp_notmem_2679 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1055) (nb078_alpha_dummy_1056 h) (nb078_wpp_notmem_2680) (nb078_wpp_notmem_2681 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1047) (nb078_alpha_dummy_1048 h) (nb078_wpp_notmem_2682) (nb078_wpp_notmem_2683 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1045) (nb078_alpha_dummy_1046 h) (nb078_wpp_notmem_2684) (nb078_wpp_notmem_2685 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1964) (nb078_wpp_notmem_1965 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))))

noncomputable def nb078_wpp_refl_0460 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_1151), (nb078_alpha_dummy_1154 h)), ((nb078_alpha_dummy_1150), (nb078_alpha_dummy_1153 h)), ((nb078_alpha_dummy_1149), (nb078_alpha_dummy_1152 h)), ((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)), ((nb078_alpha_dummy_1143), (nb078_alpha_dummy_1145 h)), ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)), ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)), ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)), ((nb078_alpha_dummy_1141), (nb078_alpha_dummy_1142 h)), ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0460 x y h)

theorem nb078_wpp_notmem_2894 : (nb078_alpha_dummy_1151) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0854)

theorem nb078_wpp_notmem_2895 (h : Var) : (nb078_alpha_dummy_1154 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0855 h)

theorem nb078_wpp_notmem_2896 : (nb078_alpha_dummy_1150) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0856)

theorem nb078_wpp_notmem_2897 (h : Var) : (nb078_alpha_dummy_1153 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0857 h)

theorem nb078_wpp_notmem_2898 : (nb078_alpha_dummy_1149) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0858)

theorem nb078_wpp_notmem_2899 (h : Var) : (nb078_alpha_dummy_1152 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0859 h)

theorem nb078_wpp_notmem_2900 : (nb078_alpha_dummy_1147) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0860)

theorem nb078_wpp_notmem_2901 (h : Var) : (nb078_alpha_dummy_1148 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0861 h)

theorem nb078_wpp_notmem_2902 : (nb078_alpha_dummy_1143) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0862)

theorem nb078_wpp_notmem_2903 (h : Var) : (nb078_alpha_dummy_1145 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0863 h)

theorem nb078_wpp_notmem_2904 : (nb078_alpha_dummy_1144) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0864)

theorem nb078_wpp_notmem_2905 (h : Var) : (nb078_alpha_dummy_1146 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0865 h)

theorem nb078_wpp_notmem_2906 : (nb078_alpha_dummy_1136) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0866)

theorem nb078_wpp_notmem_2907 (h : Var) : (nb078_alpha_dummy_1138 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0867 h)

theorem nb078_wpp_notmem_2908 : (nb078_alpha_dummy_1135) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0868)

theorem nb078_wpp_notmem_2909 (h : Var) : (nb078_alpha_dummy_1137 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0869 h)

theorem nb078_wpp_notmem_2910 : (nb078_alpha_dummy_1141) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0870)

theorem nb078_wpp_notmem_2911 (h : Var) : (nb078_alpha_dummy_1142 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0871 h)

theorem nb078_wpp_notmem_2912 : (nb078_alpha_dummy_1139) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0872)

theorem nb078_wpp_notmem_2913 (h : Var) : (nb078_alpha_dummy_1140 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0873 h)

theorem nb078_wpp_notmem_2914 : (nb078_alpha_dummy_1130) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0874)

theorem nb078_wpp_notmem_2915 (h : Var) : (nb078_alpha_dummy_1132 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0875 h)

theorem nb078_wpp_notmem_2916 : (nb078_alpha_dummy_1129) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0876)

theorem nb078_wpp_notmem_2917 (h : Var) : (nb078_alpha_dummy_1131 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0877 h)

theorem nb078_wpp_notmem_2918 : (nb078_alpha_dummy_1133) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0878)

theorem nb078_wpp_notmem_2919 (h : Var) : (nb078_alpha_dummy_1134 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0879 h)

theorem nb078_compact_envfresh_0461 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_1151), (nb078_alpha_dummy_1154 h)), ((nb078_alpha_dummy_1150), (nb078_alpha_dummy_1153 h)), ((nb078_alpha_dummy_1149), (nb078_alpha_dummy_1152 h)), ((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)), ((nb078_alpha_dummy_1143), (nb078_alpha_dummy_1145 h)), ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)), ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)), ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)), ((nb078_alpha_dummy_1141), (nb078_alpha_dummy_1142 h)), ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_1151) (nb078_alpha_dummy_1154 h) (nb078_wpp_notmem_2894) (nb078_wpp_notmem_2895 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1150) (nb078_alpha_dummy_1153 h) (nb078_wpp_notmem_2896) (nb078_wpp_notmem_2897 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1149) (nb078_alpha_dummy_1152 h) (nb078_wpp_notmem_2898) (nb078_wpp_notmem_2899 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1147) (nb078_alpha_dummy_1148 h) (nb078_wpp_notmem_2900) (nb078_wpp_notmem_2901 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1143) (nb078_alpha_dummy_1145 h) (nb078_wpp_notmem_2902) (nb078_wpp_notmem_2903 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1144) (nb078_alpha_dummy_1146 h) (nb078_wpp_notmem_2904) (nb078_wpp_notmem_2905 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1136) (nb078_alpha_dummy_1138 h) (nb078_wpp_notmem_2906) (nb078_wpp_notmem_2907 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1135) (nb078_alpha_dummy_1137 h) (nb078_wpp_notmem_2908) (nb078_wpp_notmem_2909 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1141) (nb078_alpha_dummy_1142 h) (nb078_wpp_notmem_2910) (nb078_wpp_notmem_2911 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1139) (nb078_alpha_dummy_1140 h) (nb078_wpp_notmem_2912) (nb078_wpp_notmem_2913 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1130) (nb078_alpha_dummy_1132 h) (nb078_wpp_notmem_2914) (nb078_wpp_notmem_2915 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1129) (nb078_alpha_dummy_1131 h) (nb078_wpp_notmem_2916) (nb078_wpp_notmem_2917 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1133) (nb078_alpha_dummy_1134 h) (nb078_wpp_notmem_2918) (nb078_wpp_notmem_2919 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1051) (nb078_alpha_dummy_1054 h) (nb078_wpp_notmem_2820) (nb078_wpp_notmem_2821 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1050) (nb078_alpha_dummy_1053 h) (nb078_wpp_notmem_2706) (nb078_wpp_notmem_2707 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1049) (nb078_alpha_dummy_1052 h) (nb078_wpp_notmem_2708) (nb078_wpp_notmem_2709 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1055) (nb078_alpha_dummy_1056 h) (nb078_wpp_notmem_2710) (nb078_wpp_notmem_2711 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1047) (nb078_alpha_dummy_1048 h) (nb078_wpp_notmem_2712) (nb078_wpp_notmem_2713 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1045) (nb078_alpha_dummy_1046 h) (nb078_wpp_notmem_2714) (nb078_wpp_notmem_2715 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1996) (nb078_wpp_notmem_1997 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))))

noncomputable def nb078_wpp_refl_0461 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_1151), (nb078_alpha_dummy_1154 h)), ((nb078_alpha_dummy_1150), (nb078_alpha_dummy_1153 h)), ((nb078_alpha_dummy_1149), (nb078_alpha_dummy_1152 h)), ((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)), ((nb078_alpha_dummy_1143), (nb078_alpha_dummy_1145 h)), ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)), ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)), ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)), ((nb078_alpha_dummy_1141), (nb078_alpha_dummy_1142 h)), ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0461 x y h)

theorem nb078_wpp_notmem_2920 : (nb078_alpha_dummy_1147) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0860)

theorem nb078_wpp_notmem_2921 (h : Var) : (nb078_alpha_dummy_1148 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0861 h)

theorem nb078_wpp_notmem_2922 : (nb078_alpha_dummy_1143) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0862)

theorem nb078_wpp_notmem_2923 (h : Var) : (nb078_alpha_dummy_1145 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0863 h)

theorem nb078_wpp_notmem_2924 : (nb078_alpha_dummy_1144) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0864)

theorem nb078_wpp_notmem_2925 (h : Var) : (nb078_alpha_dummy_1146 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0865 h)

theorem nb078_wpp_notmem_2926 : (nb078_alpha_dummy_1136) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0866)

theorem nb078_wpp_notmem_2927 (h : Var) : (nb078_alpha_dummy_1138 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0867 h)

theorem nb078_wpp_notmem_2928 : (nb078_alpha_dummy_1135) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0868)

theorem nb078_wpp_notmem_2929 (h : Var) : (nb078_alpha_dummy_1137 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0869 h)

theorem nb078_wpp_notmem_2930 : (nb078_alpha_dummy_1141) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0870)

theorem nb078_wpp_notmem_2931 (h : Var) : (nb078_alpha_dummy_1142 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0871 h)

theorem nb078_wpp_notmem_2932 : (nb078_alpha_dummy_1139) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0872)

theorem nb078_wpp_notmem_2933 (h : Var) : (nb078_alpha_dummy_1140 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0873 h)

theorem nb078_wpp_notmem_2934 : (nb078_alpha_dummy_1130) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0874)

theorem nb078_wpp_notmem_2935 (h : Var) : (nb078_alpha_dummy_1132 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0875 h)

theorem nb078_wpp_notmem_2936 : (nb078_alpha_dummy_1129) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0876)

theorem nb078_wpp_notmem_2937 (h : Var) : (nb078_alpha_dummy_1131 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0877 h)

theorem nb078_wpp_notmem_2938 : (nb078_alpha_dummy_1133) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0878)

theorem nb078_wpp_notmem_2939 (h : Var) : (nb078_alpha_dummy_1134 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0879 h)

theorem nb078_compact_envfresh_0462 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)), ((nb078_alpha_dummy_1143), (nb078_alpha_dummy_1145 h)), ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)), ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)), ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)), ((nb078_alpha_dummy_1141), (nb078_alpha_dummy_1142 h)), ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_1147) (nb078_alpha_dummy_1148 h) (nb078_wpp_notmem_2920) (nb078_wpp_notmem_2921 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1143) (nb078_alpha_dummy_1145 h) (nb078_wpp_notmem_2922) (nb078_wpp_notmem_2923 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1144) (nb078_alpha_dummy_1146 h) (nb078_wpp_notmem_2924) (nb078_wpp_notmem_2925 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1136) (nb078_alpha_dummy_1138 h) (nb078_wpp_notmem_2926) (nb078_wpp_notmem_2927 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1135) (nb078_alpha_dummy_1137 h) (nb078_wpp_notmem_2928) (nb078_wpp_notmem_2929 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1141) (nb078_alpha_dummy_1142 h) (nb078_wpp_notmem_2930) (nb078_wpp_notmem_2931 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1139) (nb078_alpha_dummy_1140 h) (nb078_wpp_notmem_2932) (nb078_wpp_notmem_2933 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1130) (nb078_alpha_dummy_1132 h) (nb078_wpp_notmem_2934) (nb078_wpp_notmem_2935 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1129) (nb078_alpha_dummy_1131 h) (nb078_wpp_notmem_2936) (nb078_wpp_notmem_2937 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1133) (nb078_alpha_dummy_1134 h) (nb078_wpp_notmem_2938) (nb078_wpp_notmem_2939 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1051) (nb078_alpha_dummy_1054 h) (nb078_wpp_notmem_2836) (nb078_wpp_notmem_2837 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1050) (nb078_alpha_dummy_1053 h) (nb078_wpp_notmem_2730) (nb078_wpp_notmem_2731 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1049) (nb078_alpha_dummy_1052 h) (nb078_wpp_notmem_2732) (nb078_wpp_notmem_2733 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1055) (nb078_alpha_dummy_1056 h) (nb078_wpp_notmem_2734) (nb078_wpp_notmem_2735 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1047) (nb078_alpha_dummy_1048 h) (nb078_wpp_notmem_2736) (nb078_wpp_notmem_2737 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1045) (nb078_alpha_dummy_1046 h) (nb078_wpp_notmem_2738) (nb078_wpp_notmem_2739 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_2022) (nb078_wpp_notmem_2023 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
