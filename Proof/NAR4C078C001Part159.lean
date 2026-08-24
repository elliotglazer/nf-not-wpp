import NAR4C078C001Part158

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

noncomputable def nb078_split_alpha_0139 (x : Var) (y : Var) (h : Var) : TAlphaWff [((nb078_alpha_dummy_1169), (nb078_alpha_dummy_1170 h)), ((nb078_alpha_dummy_1167), (nb078_alpha_dummy_1168 h)), ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)), ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)), ((nb078_alpha_dummy_1165), (nb078_alpha_dummy_1166 h)), ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1169)) (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_1169)) (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))))) (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1170 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_1170 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1186) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1187 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1186) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1187 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1216) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1217 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1214) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1215 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1136))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1138 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1190) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1191 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1190) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1191 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1188) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1189 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1151), (nb078_alpha_dummy_1154 h)), ((nb078_alpha_dummy_1150), (nb078_alpha_dummy_1153 h)), ((nb078_alpha_dummy_1149), (nb078_alpha_dummy_1152 h)), ((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)), ((nb078_alpha_dummy_1143), (nb078_alpha_dummy_1145 h)), ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)), ((nb078_alpha_dummy_1169), (nb078_alpha_dummy_1170 h)), ((nb078_alpha_dummy_1167), (nb078_alpha_dummy_1168 h)), ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)), ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)), ((nb078_alpha_dummy_1165), (nb078_alpha_dummy_1166 h)), ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0463 x y h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1194) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1195 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1192) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1193 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1198) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1199 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1196) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1197 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1194) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1195 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1192) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1193 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1198) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1199 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1196) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1197 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1151), (nb078_alpha_dummy_1154 h)), ((nb078_alpha_dummy_1150), (nb078_alpha_dummy_1153 h)), ((nb078_alpha_dummy_1149), (nb078_alpha_dummy_1152 h)), ((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)), ((nb078_alpha_dummy_1143), (nb078_alpha_dummy_1145 h)), ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)), ((nb078_alpha_dummy_1169), (nb078_alpha_dummy_1170 h)), ((nb078_alpha_dummy_1167), (nb078_alpha_dummy_1168 h)), ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)), ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)), ((nb078_alpha_dummy_1165), (nb078_alpha_dummy_1166 h)), ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0464 x y h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1202) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1203 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1200) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1201 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1202) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1203 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1200) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1201 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1206) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1207 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1204) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1205 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1206) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1207 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1204) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1205 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1188) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1189 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)), ((nb078_alpha_dummy_1143), (nb078_alpha_dummy_1145 h)), ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)), ((nb078_alpha_dummy_1169), (nb078_alpha_dummy_1170 h)), ((nb078_alpha_dummy_1167), (nb078_alpha_dummy_1168 h)), ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)), ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)), ((nb078_alpha_dummy_1165), (nb078_alpha_dummy_1166 h)), ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0465 x y h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1188) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1189 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1188) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1189 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)), ((nb078_alpha_dummy_1143), (nb078_alpha_dummy_1145 h)), ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)), ((nb078_alpha_dummy_1169), (nb078_alpha_dummy_1170 h)), ((nb078_alpha_dummy_1167), (nb078_alpha_dummy_1168 h)), ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)), ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)), ((nb078_alpha_dummy_1165), (nb078_alpha_dummy_1166 h)), ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0465 x y h)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1186) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1187 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1186) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1187 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1216) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1217 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1214) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1215 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1136))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1138 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1190) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1191 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1190) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1191 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1188) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1189 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1151), (nb078_alpha_dummy_1154 h)), ((nb078_alpha_dummy_1150), (nb078_alpha_dummy_1153 h)), ((nb078_alpha_dummy_1149), (nb078_alpha_dummy_1152 h)), ((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)), ((nb078_alpha_dummy_1143), (nb078_alpha_dummy_1145 h)), ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)), ((nb078_alpha_dummy_1169), (nb078_alpha_dummy_1170 h)), ((nb078_alpha_dummy_1167), (nb078_alpha_dummy_1168 h)), ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)), ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)), ((nb078_alpha_dummy_1165), (nb078_alpha_dummy_1166 h)), ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0463 x y h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1194) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1195 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1192) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1193 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1198) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1199 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1196) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1197 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1194) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1195 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1192) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1193 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1198) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1199 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1196) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1197 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1151), (nb078_alpha_dummy_1154 h)), ((nb078_alpha_dummy_1150), (nb078_alpha_dummy_1153 h)), ((nb078_alpha_dummy_1149), (nb078_alpha_dummy_1152 h)), ((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)), ((nb078_alpha_dummy_1143), (nb078_alpha_dummy_1145 h)), ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)), ((nb078_alpha_dummy_1169), (nb078_alpha_dummy_1170 h)), ((nb078_alpha_dummy_1167), (nb078_alpha_dummy_1168 h)), ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)), ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)), ((nb078_alpha_dummy_1165), (nb078_alpha_dummy_1166 h)), ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0464 x y h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1202) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1203 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1200) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1201 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1202) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1203 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1200) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1201 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1206) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1207 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1204) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1205 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1206) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1207 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1204) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1205 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1188) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1189 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)), ((nb078_alpha_dummy_1143), (nb078_alpha_dummy_1145 h)), ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)), ((nb078_alpha_dummy_1169), (nb078_alpha_dummy_1170 h)), ((nb078_alpha_dummy_1167), (nb078_alpha_dummy_1168 h)), ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)), ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)), ((nb078_alpha_dummy_1165), (nb078_alpha_dummy_1166 h)), ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0465 x y h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1188) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1189 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1188) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1189 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)), ((nb078_alpha_dummy_1143), (nb078_alpha_dummy_1145 h)), ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)), ((nb078_alpha_dummy_1169), (nb078_alpha_dummy_1170 h)), ((nb078_alpha_dummy_1167), (nb078_alpha_dummy_1168 h)), ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)), ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)), ((nb078_alpha_dummy_1165), (nb078_alpha_dummy_1166 h)), ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0465 x y h))))))))))))))))))))

theorem nb078_wpp_notmem_2958 : (nb078_alpha_dummy_1167) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0882)

theorem nb078_wpp_notmem_2959 (h : Var) : (nb078_alpha_dummy_1168 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0883 h)

theorem nb078_wpp_notmem_2960 : (nb078_alpha_dummy_1136) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0866)

theorem nb078_wpp_notmem_2961 (h : Var) : (nb078_alpha_dummy_1138 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0867 h)

theorem nb078_wpp_notmem_2962 : (nb078_alpha_dummy_1135) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0868)

theorem nb078_wpp_notmem_2963 (h : Var) : (nb078_alpha_dummy_1137 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0869 h)

theorem nb078_wpp_notmem_2964 : (nb078_alpha_dummy_1165) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0884)

theorem nb078_wpp_notmem_2965 (h : Var) : (nb078_alpha_dummy_1166 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0885 h)

theorem nb078_wpp_notmem_2966 : (nb078_alpha_dummy_1139) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0872)

theorem nb078_wpp_notmem_2967 (h : Var) : (nb078_alpha_dummy_1140 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0873 h)

theorem nb078_wpp_notmem_2968 : (nb078_alpha_dummy_1130) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0874)

theorem nb078_wpp_notmem_2969 (h : Var) : (nb078_alpha_dummy_1132 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0875 h)

theorem nb078_wpp_notmem_2970 : (nb078_alpha_dummy_1129) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0876)

theorem nb078_wpp_notmem_2971 (h : Var) : (nb078_alpha_dummy_1131 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0877 h)

theorem nb078_wpp_notmem_2972 : (nb078_alpha_dummy_1133) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0878)

theorem nb078_wpp_notmem_2973 (h : Var) : (nb078_alpha_dummy_1134 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0879 h)

theorem nb078_compact_envfresh_0466 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_1167), (nb078_alpha_dummy_1168 h)), ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)), ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)), ((nb078_alpha_dummy_1165), (nb078_alpha_dummy_1166 h)), ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_1167) (nb078_alpha_dummy_1168 h) (nb078_wpp_notmem_2958) (nb078_wpp_notmem_2959 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1136) (nb078_alpha_dummy_1138 h) (nb078_wpp_notmem_2960) (nb078_wpp_notmem_2961 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1135) (nb078_alpha_dummy_1137 h) (nb078_wpp_notmem_2962) (nb078_wpp_notmem_2963 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1165) (nb078_alpha_dummy_1166 h) (nb078_wpp_notmem_2964) (nb078_wpp_notmem_2965 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1139) (nb078_alpha_dummy_1140 h) (nb078_wpp_notmem_2966) (nb078_wpp_notmem_2967 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1130) (nb078_alpha_dummy_1132 h) (nb078_wpp_notmem_2968) (nb078_wpp_notmem_2969 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1129) (nb078_alpha_dummy_1131 h) (nb078_wpp_notmem_2970) (nb078_wpp_notmem_2971 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1133) (nb078_alpha_dummy_1134 h) (nb078_wpp_notmem_2972) (nb078_wpp_notmem_2973 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1051) (nb078_alpha_dummy_1054 h) (nb078_wpp_notmem_2866) (nb078_wpp_notmem_2867 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1050) (nb078_alpha_dummy_1053 h) (nb078_wpp_notmem_2768) (nb078_wpp_notmem_2769 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1049) (nb078_alpha_dummy_1052 h) (nb078_wpp_notmem_2770) (nb078_wpp_notmem_2771 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1055) (nb078_alpha_dummy_1056 h) (nb078_wpp_notmem_2772) (nb078_wpp_notmem_2773 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1047) (nb078_alpha_dummy_1048 h) (nb078_wpp_notmem_2774) (nb078_wpp_notmem_2775 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1045) (nb078_alpha_dummy_1046 h) (nb078_wpp_notmem_2776) (nb078_wpp_notmem_2777 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_2062) (nb078_wpp_notmem_2063 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0142) (nb078_wpp_notmem_0143 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0144) (nb078_wpp_notmem_0145 x) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))))))

noncomputable def nb078_wpp_refl_0466 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_1167), (nb078_alpha_dummy_1168 h)), ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)), ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)), ((nb078_alpha_dummy_1165), (nb078_alpha_dummy_1166 h)), ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0466 x y h)

theorem nb078_compact_fv_empty_0886 : (nb078_alpha_dummy_1187) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2974 : (nb078_alpha_dummy_1187) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0886)

theorem nb078_compact_fv_empty_0887 (h : Var) : (nb078_alpha_dummy_1190 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2975 (h : Var) : (nb078_alpha_dummy_1190 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0887 h)

theorem nb078_compact_fv_empty_0888 : (nb078_alpha_dummy_1186) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2976 : (nb078_alpha_dummy_1186) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0888)

theorem nb078_compact_fv_empty_0889 (h : Var) : (nb078_alpha_dummy_1189 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2977 (h : Var) : (nb078_alpha_dummy_1189 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0889 h)

theorem nb078_compact_fv_empty_0890 : (nb078_alpha_dummy_1185) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2978 : (nb078_alpha_dummy_1185) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0890)

theorem nb078_compact_fv_empty_0891 (h : Var) : (nb078_alpha_dummy_1188 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2979 (h : Var) : (nb078_alpha_dummy_1188 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0891 h)

theorem nb078_compact_fv_empty_0892 : (nb078_alpha_dummy_1183) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2980 : (nb078_alpha_dummy_1183) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0892)

theorem nb078_compact_fv_empty_0893 (h : Var) : (nb078_alpha_dummy_1184 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2981 (h : Var) : (nb078_alpha_dummy_1184 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0893 h)

theorem nb078_compact_fv_empty_0894 : (nb078_alpha_dummy_1179) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2982 : (nb078_alpha_dummy_1179) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0894)

theorem nb078_compact_fv_empty_0895 (h : Var) : (nb078_alpha_dummy_1181 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2983 (h : Var) : (nb078_alpha_dummy_1181 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0895 h)

theorem nb078_compact_fv_empty_0896 : (nb078_alpha_dummy_1180) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2984 : (nb078_alpha_dummy_1180) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0896)

theorem nb078_compact_fv_empty_0897 (h : Var) : (nb078_alpha_dummy_1182 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2985 (h : Var) : (nb078_alpha_dummy_1182 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0897 h)

theorem nb078_compact_fv_empty_0898 : (nb078_alpha_dummy_1172) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2986 : (nb078_alpha_dummy_1172) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0898)

theorem nb078_compact_fv_empty_0899 (h : Var) : (nb078_alpha_dummy_1174 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2987 (h : Var) : (nb078_alpha_dummy_1174 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0899 h)

theorem nb078_compact_fv_empty_0900 : (nb078_alpha_dummy_1171) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2988 : (nb078_alpha_dummy_1171) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0900)

theorem nb078_compact_fv_empty_0901 (h : Var) : (nb078_alpha_dummy_1173 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2989 (h : Var) : (nb078_alpha_dummy_1173 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0901 h)

theorem nb078_compact_fv_empty_0902 : (nb078_alpha_dummy_1177) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2990 : (nb078_alpha_dummy_1177) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0902)

theorem nb078_compact_fv_empty_0903 (h : Var) : (nb078_alpha_dummy_1178 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2991 (h : Var) : (nb078_alpha_dummy_1178 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0903 h)

theorem nb078_compact_fv_empty_0904 : (nb078_alpha_dummy_1175) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2992 : (nb078_alpha_dummy_1175) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0904)

theorem nb078_compact_fv_empty_0905 (h : Var) : (nb078_alpha_dummy_1176 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2993 (h : Var) : (nb078_alpha_dummy_1176 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0905 h)

theorem nb078_compact_envfresh_0467 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_1187), (nb078_alpha_dummy_1190 h)), ((nb078_alpha_dummy_1186), (nb078_alpha_dummy_1189 h)), ((nb078_alpha_dummy_1185), (nb078_alpha_dummy_1188 h)), ((nb078_alpha_dummy_1183), (nb078_alpha_dummy_1184 h)), ((nb078_alpha_dummy_1179), (nb078_alpha_dummy_1181 h)), ((nb078_alpha_dummy_1180), (nb078_alpha_dummy_1182 h)), ((nb078_alpha_dummy_1172), (nb078_alpha_dummy_1174 h)), ((nb078_alpha_dummy_1171), (nb078_alpha_dummy_1173 h)), ((nb078_alpha_dummy_1177), (nb078_alpha_dummy_1178 h)), ((nb078_alpha_dummy_1175), (nb078_alpha_dummy_1176 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_1187) (nb078_alpha_dummy_1190 h) (nb078_wpp_notmem_2974) (nb078_wpp_notmem_2975 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1186) (nb078_alpha_dummy_1189 h) (nb078_wpp_notmem_2976) (nb078_wpp_notmem_2977 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1185) (nb078_alpha_dummy_1188 h) (nb078_wpp_notmem_2978) (nb078_wpp_notmem_2979 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1183) (nb078_alpha_dummy_1184 h) (nb078_wpp_notmem_2980) (nb078_wpp_notmem_2981 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1179) (nb078_alpha_dummy_1181 h) (nb078_wpp_notmem_2982) (nb078_wpp_notmem_2983 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1180) (nb078_alpha_dummy_1182 h) (nb078_wpp_notmem_2984) (nb078_wpp_notmem_2985 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1172) (nb078_alpha_dummy_1174 h) (nb078_wpp_notmem_2986) (nb078_wpp_notmem_2987 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1171) (nb078_alpha_dummy_1173 h) (nb078_wpp_notmem_2988) (nb078_wpp_notmem_2989 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1177) (nb078_alpha_dummy_1178 h) (nb078_wpp_notmem_2990) (nb078_wpp_notmem_2991 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1175) (nb078_alpha_dummy_1176 h) (nb078_wpp_notmem_2992) (nb078_wpp_notmem_2993 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1130) (nb078_alpha_dummy_1132 h) (nb078_wpp_notmem_2888) (nb078_wpp_notmem_2889 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1129) (nb078_alpha_dummy_1131 h) (nb078_wpp_notmem_2890) (nb078_wpp_notmem_2891 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1133) (nb078_alpha_dummy_1134 h) (nb078_wpp_notmem_2892) (nb078_wpp_notmem_2893 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1051) (nb078_alpha_dummy_1054 h) (nb078_wpp_notmem_2798) (nb078_wpp_notmem_2799 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1050) (nb078_alpha_dummy_1053 h) (nb078_wpp_notmem_2676) (nb078_wpp_notmem_2677 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1049) (nb078_alpha_dummy_1052 h) (nb078_wpp_notmem_2678) (nb078_wpp_notmem_2679 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1055) (nb078_alpha_dummy_1056 h) (nb078_wpp_notmem_2680) (nb078_wpp_notmem_2681 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1047) (nb078_alpha_dummy_1048 h) (nb078_wpp_notmem_2682) (nb078_wpp_notmem_2683 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1045) (nb078_alpha_dummy_1046 h) (nb078_wpp_notmem_2684) (nb078_wpp_notmem_2685 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1964) (nb078_wpp_notmem_1965 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))))

noncomputable def nb078_wpp_refl_0467 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_1187), (nb078_alpha_dummy_1190 h)), ((nb078_alpha_dummy_1186), (nb078_alpha_dummy_1189 h)), ((nb078_alpha_dummy_1185), (nb078_alpha_dummy_1188 h)), ((nb078_alpha_dummy_1183), (nb078_alpha_dummy_1184 h)), ((nb078_alpha_dummy_1179), (nb078_alpha_dummy_1181 h)), ((nb078_alpha_dummy_1180), (nb078_alpha_dummy_1182 h)), ((nb078_alpha_dummy_1172), (nb078_alpha_dummy_1174 h)), ((nb078_alpha_dummy_1171), (nb078_alpha_dummy_1173 h)), ((nb078_alpha_dummy_1177), (nb078_alpha_dummy_1178 h)), ((nb078_alpha_dummy_1175), (nb078_alpha_dummy_1176 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0467 x y h)

theorem nb078_wpp_notmem_2994 : (nb078_alpha_dummy_1187) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0886)

theorem nb078_wpp_notmem_2995 (h : Var) : (nb078_alpha_dummy_1190 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0887 h)

theorem nb078_wpp_notmem_2996 : (nb078_alpha_dummy_1186) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0888)

theorem nb078_wpp_notmem_2997 (h : Var) : (nb078_alpha_dummy_1189 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0889 h)

theorem nb078_wpp_notmem_2998 : (nb078_alpha_dummy_1185) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0890)

theorem nb078_wpp_notmem_2999 (h : Var) : (nb078_alpha_dummy_1188 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0891 h)

theorem nb078_wpp_notmem_3000 : (nb078_alpha_dummy_1183) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0892)

theorem nb078_wpp_notmem_3001 (h : Var) : (nb078_alpha_dummy_1184 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0893 h)

theorem nb078_wpp_notmem_3002 : (nb078_alpha_dummy_1179) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0894)

theorem nb078_wpp_notmem_3003 (h : Var) : (nb078_alpha_dummy_1181 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0895 h)

theorem nb078_wpp_notmem_3004 : (nb078_alpha_dummy_1180) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0896)

theorem nb078_wpp_notmem_3005 (h : Var) : (nb078_alpha_dummy_1182 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0897 h)

theorem nb078_wpp_notmem_3006 : (nb078_alpha_dummy_1172) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0898)

theorem nb078_wpp_notmem_3007 (h : Var) : (nb078_alpha_dummy_1174 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0899 h)

theorem nb078_wpp_notmem_3008 : (nb078_alpha_dummy_1171) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0900)

theorem nb078_wpp_notmem_3009 (h : Var) : (nb078_alpha_dummy_1173 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0901 h)

theorem nb078_wpp_notmem_3010 : (nb078_alpha_dummy_1177) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0902)

theorem nb078_wpp_notmem_3011 (h : Var) : (nb078_alpha_dummy_1178 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0903 h)

theorem nb078_wpp_notmem_3012 : (nb078_alpha_dummy_1175) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0904)

theorem nb078_wpp_notmem_3013 (h : Var) : (nb078_alpha_dummy_1176 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0905 h)

theorem nb078_compact_envfresh_0468 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_1187), (nb078_alpha_dummy_1190 h)), ((nb078_alpha_dummy_1186), (nb078_alpha_dummy_1189 h)), ((nb078_alpha_dummy_1185), (nb078_alpha_dummy_1188 h)), ((nb078_alpha_dummy_1183), (nb078_alpha_dummy_1184 h)), ((nb078_alpha_dummy_1179), (nb078_alpha_dummy_1181 h)), ((nb078_alpha_dummy_1180), (nb078_alpha_dummy_1182 h)), ((nb078_alpha_dummy_1172), (nb078_alpha_dummy_1174 h)), ((nb078_alpha_dummy_1171), (nb078_alpha_dummy_1173 h)), ((nb078_alpha_dummy_1177), (nb078_alpha_dummy_1178 h)), ((nb078_alpha_dummy_1175), (nb078_alpha_dummy_1176 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_1187) (nb078_alpha_dummy_1190 h) (nb078_wpp_notmem_2994) (nb078_wpp_notmem_2995 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1186) (nb078_alpha_dummy_1189 h) (nb078_wpp_notmem_2996) (nb078_wpp_notmem_2997 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1185) (nb078_alpha_dummy_1188 h) (nb078_wpp_notmem_2998) (nb078_wpp_notmem_2999 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1183) (nb078_alpha_dummy_1184 h) (nb078_wpp_notmem_3000) (nb078_wpp_notmem_3001 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1179) (nb078_alpha_dummy_1181 h) (nb078_wpp_notmem_3002) (nb078_wpp_notmem_3003 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1180) (nb078_alpha_dummy_1182 h) (nb078_wpp_notmem_3004) (nb078_wpp_notmem_3005 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1172) (nb078_alpha_dummy_1174 h) (nb078_wpp_notmem_3006) (nb078_wpp_notmem_3007 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1171) (nb078_alpha_dummy_1173 h) (nb078_wpp_notmem_3008) (nb078_wpp_notmem_3009 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1177) (nb078_alpha_dummy_1178 h) (nb078_wpp_notmem_3010) (nb078_wpp_notmem_3011 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1175) (nb078_alpha_dummy_1176 h) (nb078_wpp_notmem_3012) (nb078_wpp_notmem_3013 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1130) (nb078_alpha_dummy_1132 h) (nb078_wpp_notmem_2914) (nb078_wpp_notmem_2915 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1129) (nb078_alpha_dummy_1131 h) (nb078_wpp_notmem_2916) (nb078_wpp_notmem_2917 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1133) (nb078_alpha_dummy_1134 h) (nb078_wpp_notmem_2918) (nb078_wpp_notmem_2919 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1051) (nb078_alpha_dummy_1054 h) (nb078_wpp_notmem_2820) (nb078_wpp_notmem_2821 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1050) (nb078_alpha_dummy_1053 h) (nb078_wpp_notmem_2706) (nb078_wpp_notmem_2707 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1049) (nb078_alpha_dummy_1052 h) (nb078_wpp_notmem_2708) (nb078_wpp_notmem_2709 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1055) (nb078_alpha_dummy_1056 h) (nb078_wpp_notmem_2710) (nb078_wpp_notmem_2711 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1047) (nb078_alpha_dummy_1048 h) (nb078_wpp_notmem_2712) (nb078_wpp_notmem_2713 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1045) (nb078_alpha_dummy_1046 h) (nb078_wpp_notmem_2714) (nb078_wpp_notmem_2715 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1996) (nb078_wpp_notmem_1997 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))))

noncomputable def nb078_wpp_refl_0468 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_1187), (nb078_alpha_dummy_1190 h)), ((nb078_alpha_dummy_1186), (nb078_alpha_dummy_1189 h)), ((nb078_alpha_dummy_1185), (nb078_alpha_dummy_1188 h)), ((nb078_alpha_dummy_1183), (nb078_alpha_dummy_1184 h)), ((nb078_alpha_dummy_1179), (nb078_alpha_dummy_1181 h)), ((nb078_alpha_dummy_1180), (nb078_alpha_dummy_1182 h)), ((nb078_alpha_dummy_1172), (nb078_alpha_dummy_1174 h)), ((nb078_alpha_dummy_1171), (nb078_alpha_dummy_1173 h)), ((nb078_alpha_dummy_1177), (nb078_alpha_dummy_1178 h)), ((nb078_alpha_dummy_1175), (nb078_alpha_dummy_1176 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0468 x y h)

theorem nb078_wpp_notmem_3014 : (nb078_alpha_dummy_1183) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0892)

theorem nb078_wpp_notmem_3015 (h : Var) : (nb078_alpha_dummy_1184 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0893 h)

theorem nb078_wpp_notmem_3016 : (nb078_alpha_dummy_1179) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0894)

theorem nb078_wpp_notmem_3017 (h : Var) : (nb078_alpha_dummy_1181 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0895 h)

theorem nb078_wpp_notmem_3018 : (nb078_alpha_dummy_1180) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0896)

theorem nb078_wpp_notmem_3019 (h : Var) : (nb078_alpha_dummy_1182 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0897 h)

theorem nb078_wpp_notmem_3020 : (nb078_alpha_dummy_1172) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0898)

theorem nb078_wpp_notmem_3021 (h : Var) : (nb078_alpha_dummy_1174 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0899 h)

theorem nb078_wpp_notmem_3022 : (nb078_alpha_dummy_1171) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0900)

theorem nb078_wpp_notmem_3023 (h : Var) : (nb078_alpha_dummy_1173 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0901 h)

theorem nb078_wpp_notmem_3024 : (nb078_alpha_dummy_1177) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0902)

theorem nb078_wpp_notmem_3025 (h : Var) : (nb078_alpha_dummy_1178 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0903 h)

theorem nb078_wpp_notmem_3026 : (nb078_alpha_dummy_1175) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0904)

theorem nb078_wpp_notmem_3027 (h : Var) : (nb078_alpha_dummy_1176 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0905 h)

theorem nb078_compact_envfresh_0469 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_1183), (nb078_alpha_dummy_1184 h)), ((nb078_alpha_dummy_1179), (nb078_alpha_dummy_1181 h)), ((nb078_alpha_dummy_1180), (nb078_alpha_dummy_1182 h)), ((nb078_alpha_dummy_1172), (nb078_alpha_dummy_1174 h)), ((nb078_alpha_dummy_1171), (nb078_alpha_dummy_1173 h)), ((nb078_alpha_dummy_1177), (nb078_alpha_dummy_1178 h)), ((nb078_alpha_dummy_1175), (nb078_alpha_dummy_1176 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_1183) (nb078_alpha_dummy_1184 h) (nb078_wpp_notmem_3014) (nb078_wpp_notmem_3015 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1179) (nb078_alpha_dummy_1181 h) (nb078_wpp_notmem_3016) (nb078_wpp_notmem_3017 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1180) (nb078_alpha_dummy_1182 h) (nb078_wpp_notmem_3018) (nb078_wpp_notmem_3019 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1172) (nb078_alpha_dummy_1174 h) (nb078_wpp_notmem_3020) (nb078_wpp_notmem_3021 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1171) (nb078_alpha_dummy_1173 h) (nb078_wpp_notmem_3022) (nb078_wpp_notmem_3023 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1177) (nb078_alpha_dummy_1178 h) (nb078_wpp_notmem_3024) (nb078_wpp_notmem_3025 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1175) (nb078_alpha_dummy_1176 h) (nb078_wpp_notmem_3026) (nb078_wpp_notmem_3027 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1130) (nb078_alpha_dummy_1132 h) (nb078_wpp_notmem_2934) (nb078_wpp_notmem_2935 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1129) (nb078_alpha_dummy_1131 h) (nb078_wpp_notmem_2936) (nb078_wpp_notmem_2937 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1133) (nb078_alpha_dummy_1134 h) (nb078_wpp_notmem_2938) (nb078_wpp_notmem_2939 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1051) (nb078_alpha_dummy_1054 h) (nb078_wpp_notmem_2836) (nb078_wpp_notmem_2837 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1050) (nb078_alpha_dummy_1053 h) (nb078_wpp_notmem_2730) (nb078_wpp_notmem_2731 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1049) (nb078_alpha_dummy_1052 h) (nb078_wpp_notmem_2732) (nb078_wpp_notmem_2733 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1055) (nb078_alpha_dummy_1056 h) (nb078_wpp_notmem_2734) (nb078_wpp_notmem_2735 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1047) (nb078_alpha_dummy_1048 h) (nb078_wpp_notmem_2736) (nb078_wpp_notmem_2737 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1045) (nb078_alpha_dummy_1046 h) (nb078_wpp_notmem_2738) (nb078_wpp_notmem_2739 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_2022) (nb078_wpp_notmem_2023 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
