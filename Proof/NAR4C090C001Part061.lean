import NAR4C090C001Part060

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

theorem nb090_compact_envfresh_0137 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_447 A), (nb090_alpha_dummy_450 h)), ((nb090_alpha_dummy_446 A), (nb090_alpha_dummy_449 h)), ((nb090_alpha_dummy_445 A), (nb090_alpha_dummy_448 h)), ((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)), ((nb090_alpha_dummy_439 A), (nb090_alpha_dummy_441 h)), ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)), ((nb090_alpha_dummy_465 A), (nb090_alpha_dummy_466 h)), ((nb090_alpha_dummy_463 A), (nb090_alpha_dummy_464 h)), ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)), ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_461 A), (nb090_alpha_dummy_462 h)), ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_447 A) (nb090_alpha_dummy_450 h) (nb090_wpp_notmem_1132 A) (nb090_wpp_notmem_1133 h) (TEnvFresh.consFresh (nb090_alpha_dummy_446 A) (nb090_alpha_dummy_449 h) (nb090_wpp_notmem_1134 A) (nb090_wpp_notmem_1135 h) (TEnvFresh.consFresh (nb090_alpha_dummy_445 A) (nb090_alpha_dummy_448 h) (nb090_wpp_notmem_1136 A) (nb090_wpp_notmem_1137 h) (TEnvFresh.consFresh (nb090_alpha_dummy_443 A) (nb090_alpha_dummy_444 h) (nb090_wpp_notmem_1138 A) (nb090_wpp_notmem_1139 h) (TEnvFresh.consFresh (nb090_alpha_dummy_439 A) (nb090_alpha_dummy_441 h) (nb090_wpp_notmem_1140 A) (nb090_wpp_notmem_1141 h) (TEnvFresh.consFresh (nb090_alpha_dummy_440 A) (nb090_alpha_dummy_442 h) (nb090_wpp_notmem_1142 A) (nb090_wpp_notmem_1143 h) (TEnvFresh.consFresh (nb090_alpha_dummy_465 A) (nb090_alpha_dummy_466 h) (nb090_wpp_notmem_1192 A) (nb090_wpp_notmem_1193 h) (TEnvFresh.consFresh (nb090_alpha_dummy_463 A) (nb090_alpha_dummy_464 h) (nb090_wpp_notmem_1194 A) (nb090_wpp_notmem_1195 h) (TEnvFresh.consFresh (nb090_alpha_dummy_432 A) (nb090_alpha_dummy_434 h) (nb090_wpp_notmem_1144 A) (nb090_wpp_notmem_1145 h) (TEnvFresh.consFresh (nb090_alpha_dummy_431 A) (nb090_alpha_dummy_433 h) (nb090_wpp_notmem_1146 A) (nb090_wpp_notmem_1147 h) (TEnvFresh.consFresh (nb090_alpha_dummy_461 A) (nb090_alpha_dummy_462 h) (nb090_wpp_notmem_1196 A) (nb090_wpp_notmem_1197 h) (TEnvFresh.consFresh (nb090_alpha_dummy_435 A) (nb090_alpha_dummy_436 h) (nb090_wpp_notmem_1150 A) (nb090_wpp_notmem_1151 h) (TEnvFresh.consFresh (nb090_alpha_dummy_424 A) (nb090_alpha_dummy_427 h) (nb090_wpp_notmem_1152 A) (nb090_wpp_notmem_1153 h) (TEnvFresh.consFresh (nb090_alpha_dummy_423 A) (nb090_alpha_dummy_426 h) (nb090_wpp_notmem_1154 A) (nb090_wpp_notmem_1155 h) (TEnvFresh.consFresh (nb090_alpha_dummy_429 A) (nb090_alpha_dummy_430 h) (nb090_wpp_notmem_1156 A) (nb090_wpp_notmem_1157 h) (TEnvFresh.consFresh (nb090_alpha_dummy_421 A) (nb090_alpha_dummy_422 h) (nb090_wpp_notmem_1158 A) (nb090_wpp_notmem_1159 h) (TEnvFresh.consFresh (nb090_alpha_dummy_419 A) (nb090_alpha_dummy_420 h) (nb090_wpp_notmem_1160 A) (nb090_wpp_notmem_1161 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0174 A) (nb090_wpp_notmem_0175 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0046 A) (nb090_wpp_notmem_0047 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0048 A) (nb090_wpp_notmem_0049 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0050 A) (nb090_wpp_notmem_0051 v u A h) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))))

noncomputable def nb090_wpp_refl_0137 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_447 A), (nb090_alpha_dummy_450 h)), ((nb090_alpha_dummy_446 A), (nb090_alpha_dummy_449 h)), ((nb090_alpha_dummy_445 A), (nb090_alpha_dummy_448 h)), ((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)), ((nb090_alpha_dummy_439 A), (nb090_alpha_dummy_441 h)), ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)), ((nb090_alpha_dummy_465 A), (nb090_alpha_dummy_466 h)), ((nb090_alpha_dummy_463 A), (nb090_alpha_dummy_464 h)), ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)), ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_461 A), (nb090_alpha_dummy_462 h)), ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0137 v u A h)

theorem nb090_wpp_notmem_1198 (A : Class) : (nb090_alpha_dummy_465 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_465, fv_syn_cnnc] using (nb090_compact_fv_empty_0344 A)

theorem nb090_wpp_notmem_1199 (h : Var) : (nb090_alpha_dummy_466 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_466, fv_syn_cnnc] using (nb090_compact_fv_empty_0345 h)

theorem nb090_wpp_notmem_1200 (A : Class) : (nb090_alpha_dummy_463 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_463, fv_syn_cnnc] using (nb090_compact_fv_empty_0346 A)

theorem nb090_wpp_notmem_1201 (h : Var) : (nb090_alpha_dummy_464 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_464, fv_syn_cnnc] using (nb090_compact_fv_empty_0347 h)

theorem nb090_wpp_notmem_1202 (A : Class) : (nb090_alpha_dummy_461 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_461, fv_syn_cnnc] using (nb090_compact_fv_empty_0348 A)

theorem nb090_wpp_notmem_1203 (h : Var) : (nb090_alpha_dummy_462 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_462, fv_syn_cnnc] using (nb090_compact_fv_empty_0349 h)

theorem nb090_compact_envfresh_0138 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)), ((nb090_alpha_dummy_439 A), (nb090_alpha_dummy_441 h)), ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)), ((nb090_alpha_dummy_465 A), (nb090_alpha_dummy_466 h)), ((nb090_alpha_dummy_463 A), (nb090_alpha_dummy_464 h)), ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)), ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_461 A), (nb090_alpha_dummy_462 h)), ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_443 A) (nb090_alpha_dummy_444 h) (nb090_wpp_notmem_1162 A) (nb090_wpp_notmem_1163 h) (TEnvFresh.consFresh (nb090_alpha_dummy_439 A) (nb090_alpha_dummy_441 h) (nb090_wpp_notmem_1164 A) (nb090_wpp_notmem_1165 h) (TEnvFresh.consFresh (nb090_alpha_dummy_440 A) (nb090_alpha_dummy_442 h) (nb090_wpp_notmem_1166 A) (nb090_wpp_notmem_1167 h) (TEnvFresh.consFresh (nb090_alpha_dummy_465 A) (nb090_alpha_dummy_466 h) (nb090_wpp_notmem_1198 A) (nb090_wpp_notmem_1199 h) (TEnvFresh.consFresh (nb090_alpha_dummy_463 A) (nb090_alpha_dummy_464 h) (nb090_wpp_notmem_1200 A) (nb090_wpp_notmem_1201 h) (TEnvFresh.consFresh (nb090_alpha_dummy_432 A) (nb090_alpha_dummy_434 h) (nb090_wpp_notmem_1168 A) (nb090_wpp_notmem_1169 h) (TEnvFresh.consFresh (nb090_alpha_dummy_431 A) (nb090_alpha_dummy_433 h) (nb090_wpp_notmem_1170 A) (nb090_wpp_notmem_1171 h) (TEnvFresh.consFresh (nb090_alpha_dummy_461 A) (nb090_alpha_dummy_462 h) (nb090_wpp_notmem_1202 A) (nb090_wpp_notmem_1203 h) (TEnvFresh.consFresh (nb090_alpha_dummy_435 A) (nb090_alpha_dummy_436 h) (nb090_wpp_notmem_1174 A) (nb090_wpp_notmem_1175 h) (TEnvFresh.consFresh (nb090_alpha_dummy_424 A) (nb090_alpha_dummy_427 h) (nb090_wpp_notmem_1176 A) (nb090_wpp_notmem_1177 h) (TEnvFresh.consFresh (nb090_alpha_dummy_423 A) (nb090_alpha_dummy_426 h) (nb090_wpp_notmem_1178 A) (nb090_wpp_notmem_1179 h) (TEnvFresh.consFresh (nb090_alpha_dummy_429 A) (nb090_alpha_dummy_430 h) (nb090_wpp_notmem_1180 A) (nb090_wpp_notmem_1181 h) (TEnvFresh.consFresh (nb090_alpha_dummy_421 A) (nb090_alpha_dummy_422 h) (nb090_wpp_notmem_1182 A) (nb090_wpp_notmem_1183 h) (TEnvFresh.consFresh (nb090_alpha_dummy_419 A) (nb090_alpha_dummy_420 h) (nb090_wpp_notmem_1184 A) (nb090_wpp_notmem_1185 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0200 A) (nb090_wpp_notmem_0201 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0066 A) (nb090_wpp_notmem_0067 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0068 A) (nb090_wpp_notmem_0069 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0070 A) (nb090_wpp_notmem_0071 v u A h) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))))

noncomputable def nb090_wpp_refl_0138 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)), ((nb090_alpha_dummy_439 A), (nb090_alpha_dummy_441 h)), ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)), ((nb090_alpha_dummy_465 A), (nb090_alpha_dummy_466 h)), ((nb090_alpha_dummy_463 A), (nb090_alpha_dummy_464 h)), ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)), ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_461 A), (nb090_alpha_dummy_462 h)), ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0138 v u A h)

noncomputable def nb090_split_alpha_0039 (v : Var) (u : Var) (A : Class) (h : Var) : TAlphaWff [((nb090_alpha_dummy_463 A), (nb090_alpha_dummy_464 h)), ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)), ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_461 A), (nb090_alpha_dummy_462 h)), ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (Wff.classMem (Class.cv (nb090_alpha_dummy_463 A)) (syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))))) (Wff.classMem (Class.cv (nb090_alpha_dummy_464 h)) (syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0442 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0443 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0442 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0443 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0472 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0473 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0470 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0471 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_432 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_434 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0446 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0447 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0446 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0447 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0444 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0445 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_447 A), (nb090_alpha_dummy_450 h)), ((nb090_alpha_dummy_446 A), (nb090_alpha_dummy_449 h)), ((nb090_alpha_dummy_445 A), (nb090_alpha_dummy_448 h)), ((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)), ((nb090_alpha_dummy_439 A), (nb090_alpha_dummy_441 h)), ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)), ((nb090_alpha_dummy_465 A), (nb090_alpha_dummy_466 h)), ((nb090_alpha_dummy_463 A), (nb090_alpha_dummy_464 h)), ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)), ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_461 A), (nb090_alpha_dummy_462 h)), ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0136 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0450 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0451 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0448 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0449 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0454 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0455 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0452 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0453 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0450 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0451 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0448 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0449 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0454 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0455 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0452 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0453 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_447 A), (nb090_alpha_dummy_450 h)), ((nb090_alpha_dummy_446 A), (nb090_alpha_dummy_449 h)), ((nb090_alpha_dummy_445 A), (nb090_alpha_dummy_448 h)), ((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)), ((nb090_alpha_dummy_439 A), (nb090_alpha_dummy_441 h)), ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)), ((nb090_alpha_dummy_465 A), (nb090_alpha_dummy_466 h)), ((nb090_alpha_dummy_463 A), (nb090_alpha_dummy_464 h)), ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)), ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_461 A), (nb090_alpha_dummy_462 h)), ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0137 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0458 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0459 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0456 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0457 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0458 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0459 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0456 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0457 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0462 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0463 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0460 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0461 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0462 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0463 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0460 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0461 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0444 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0445 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)), ((nb090_alpha_dummy_439 A), (nb090_alpha_dummy_441 h)), ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)), ((nb090_alpha_dummy_465 A), (nb090_alpha_dummy_466 h)), ((nb090_alpha_dummy_463 A), (nb090_alpha_dummy_464 h)), ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)), ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_461 A), (nb090_alpha_dummy_462 h)), ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0138 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0444 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0445 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0444 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0445 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)), ((nb090_alpha_dummy_439 A), (nb090_alpha_dummy_441 h)), ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)), ((nb090_alpha_dummy_465 A), (nb090_alpha_dummy_466 h)), ((nb090_alpha_dummy_463 A), (nb090_alpha_dummy_464 h)), ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)), ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_461 A), (nb090_alpha_dummy_462 h)), ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0138 v u A h)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0442 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0443 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0442 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0443 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0472 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0473 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0470 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0471 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_432 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_434 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0446 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0447 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0446 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0447 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0444 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0445 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_447 A), (nb090_alpha_dummy_450 h)), ((nb090_alpha_dummy_446 A), (nb090_alpha_dummy_449 h)), ((nb090_alpha_dummy_445 A), (nb090_alpha_dummy_448 h)), ((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)), ((nb090_alpha_dummy_439 A), (nb090_alpha_dummy_441 h)), ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)), ((nb090_alpha_dummy_465 A), (nb090_alpha_dummy_466 h)), ((nb090_alpha_dummy_463 A), (nb090_alpha_dummy_464 h)), ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)), ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_461 A), (nb090_alpha_dummy_462 h)), ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0136 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0450 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0451 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0448 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0449 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0454 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0455 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0452 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0453 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0450 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0451 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0448 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0449 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0454 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0455 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0452 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0453 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_447 A), (nb090_alpha_dummy_450 h)), ((nb090_alpha_dummy_446 A), (nb090_alpha_dummy_449 h)), ((nb090_alpha_dummy_445 A), (nb090_alpha_dummy_448 h)), ((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)), ((nb090_alpha_dummy_439 A), (nb090_alpha_dummy_441 h)), ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)), ((nb090_alpha_dummy_465 A), (nb090_alpha_dummy_466 h)), ((nb090_alpha_dummy_463 A), (nb090_alpha_dummy_464 h)), ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)), ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_461 A), (nb090_alpha_dummy_462 h)), ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0137 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0458 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0459 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0456 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0457 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0458 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0459 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0456 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0457 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0462 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0463 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0460 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0461 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0462 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0463 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0460 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0461 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0444 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0445 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)), ((nb090_alpha_dummy_439 A), (nb090_alpha_dummy_441 h)), ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)), ((nb090_alpha_dummy_465 A), (nb090_alpha_dummy_466 h)), ((nb090_alpha_dummy_463 A), (nb090_alpha_dummy_464 h)), ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)), ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_461 A), (nb090_alpha_dummy_462 h)), ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0138 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0444 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0445 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0444 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0445 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)), ((nb090_alpha_dummy_439 A), (nb090_alpha_dummy_441 h)), ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)), ((nb090_alpha_dummy_465 A), (nb090_alpha_dummy_466 h)), ((nb090_alpha_dummy_463 A), (nb090_alpha_dummy_464 h)), ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)), ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_461 A), (nb090_alpha_dummy_462 h)), ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0138 v u A h))))))))))))))))))))))))

theorem nb090_wpp_notmem_1204 (A : Class) : (nb090_alpha_dummy_463 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_463, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0346 A)

theorem nb090_wpp_notmem_1205 (h : Var) : (nb090_alpha_dummy_464 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_464, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0347 h)

theorem nb090_wpp_notmem_1206 (A : Class) : (nb090_alpha_dummy_432 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_432, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0326 A)

theorem nb090_wpp_notmem_1207 (h : Var) : (nb090_alpha_dummy_434 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_434, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0327 h)

theorem nb090_wpp_notmem_1208 (A : Class) : (nb090_alpha_dummy_431 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_431, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0328 A)

theorem nb090_wpp_notmem_1209 (h : Var) : (nb090_alpha_dummy_433 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_433, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0329 h)

theorem nb090_wpp_notmem_1210 (A : Class) : (nb090_alpha_dummy_461 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_461, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0348 A)

theorem nb090_wpp_notmem_1211 (h : Var) : (nb090_alpha_dummy_462 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_462, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0349 h)

theorem nb090_wpp_notmem_1212 (A : Class) : (nb090_alpha_dummy_435 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_435, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0332 A)

theorem nb090_wpp_notmem_1213 (h : Var) : (nb090_alpha_dummy_436 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_436, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0333 h)

theorem nb090_wpp_notmem_1214 (A : Class) : (nb090_alpha_dummy_424 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_424, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0334 A)

theorem nb090_wpp_notmem_1215 (h : Var) : (nb090_alpha_dummy_427 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_427, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0335 h)

theorem nb090_wpp_notmem_1216 (A : Class) : (nb090_alpha_dummy_423 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_423, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0336 A)

theorem nb090_wpp_notmem_1217 (h : Var) : (nb090_alpha_dummy_426 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_426, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0337 h)

theorem nb090_wpp_notmem_1218 (A : Class) : (nb090_alpha_dummy_429 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_429, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0338 A)

theorem nb090_wpp_notmem_1219 (h : Var) : (nb090_alpha_dummy_430 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_430, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0339 h)

theorem nb090_wpp_notmem_1220 (A : Class) : (nb090_alpha_dummy_421 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_421, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0340 A)

theorem nb090_wpp_notmem_1221 (h : Var) : (nb090_alpha_dummy_422 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_422, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0341 h)

theorem nb090_wpp_notmem_1222 (A : Class) : (nb090_alpha_dummy_419 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_419, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0342 A)

theorem nb090_wpp_notmem_1223 (h : Var) : (nb090_alpha_dummy_420 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_420, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0343 h)

theorem nb090_compact_envfresh_0139 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_463 A), (nb090_alpha_dummy_464 h)), ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)), ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_461 A), (nb090_alpha_dummy_462 h)), ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_463 A) (nb090_alpha_dummy_464 h) (nb090_wpp_notmem_1204 A) (nb090_wpp_notmem_1205 h) (TEnvFresh.consFresh (nb090_alpha_dummy_432 A) (nb090_alpha_dummy_434 h) (nb090_wpp_notmem_1206 A) (nb090_wpp_notmem_1207 h) (TEnvFresh.consFresh (nb090_alpha_dummy_431 A) (nb090_alpha_dummy_433 h) (nb090_wpp_notmem_1208 A) (nb090_wpp_notmem_1209 h) (TEnvFresh.consFresh (nb090_alpha_dummy_461 A) (nb090_alpha_dummy_462 h) (nb090_wpp_notmem_1210 A) (nb090_wpp_notmem_1211 h) (TEnvFresh.consFresh (nb090_alpha_dummy_435 A) (nb090_alpha_dummy_436 h) (nb090_wpp_notmem_1212 A) (nb090_wpp_notmem_1213 h) (TEnvFresh.consFresh (nb090_alpha_dummy_424 A) (nb090_alpha_dummy_427 h) (nb090_wpp_notmem_1214 A) (nb090_wpp_notmem_1215 h) (TEnvFresh.consFresh (nb090_alpha_dummy_423 A) (nb090_alpha_dummy_426 h) (nb090_wpp_notmem_1216 A) (nb090_wpp_notmem_1217 h) (TEnvFresh.consFresh (nb090_alpha_dummy_429 A) (nb090_alpha_dummy_430 h) (nb090_wpp_notmem_1218 A) (nb090_wpp_notmem_1219 h) (TEnvFresh.consFresh (nb090_alpha_dummy_421 A) (nb090_alpha_dummy_422 h) (nb090_wpp_notmem_1220 A) (nb090_wpp_notmem_1221 h) (TEnvFresh.consFresh (nb090_alpha_dummy_419 A) (nb090_alpha_dummy_420 h) (nb090_wpp_notmem_1222 A) (nb090_wpp_notmem_1223 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0240 A) (nb090_wpp_notmem_0241 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0100 A) (nb090_wpp_notmem_0101 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0102 A) (nb090_wpp_notmem_0103 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0104 A) (nb090_wpp_notmem_0105 v u A h) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))))))

noncomputable def nb090_wpp_refl_0139 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_463 A), (nb090_alpha_dummy_464 h)), ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)), ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_461 A), (nb090_alpha_dummy_462 h)), ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0139 v u A h)

theorem nb090_compact_fv_empty_0350 (A : Class) : (nb090_alpha_dummy_483 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1224 (A : Class) : (nb090_alpha_dummy_483 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_483, fv_syn_c1c] using (nb090_compact_fv_empty_0350 A)

theorem nb090_compact_fv_empty_0351 (h : Var) : (nb090_alpha_dummy_486 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1225 (h : Var) : (nb090_alpha_dummy_486 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_486, fv_syn_c1c] using (nb090_compact_fv_empty_0351 h)

theorem nb090_compact_fv_empty_0352 (A : Class) : (nb090_alpha_dummy_482 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1226 (A : Class) : (nb090_alpha_dummy_482 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_482, fv_syn_c1c] using (nb090_compact_fv_empty_0352 A)

theorem nb090_compact_fv_empty_0353 (h : Var) : (nb090_alpha_dummy_485 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1227 (h : Var) : (nb090_alpha_dummy_485 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_485, fv_syn_c1c] using (nb090_compact_fv_empty_0353 h)

theorem nb090_compact_fv_empty_0354 (A : Class) : (nb090_alpha_dummy_481 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1228 (A : Class) : (nb090_alpha_dummy_481 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_481, fv_syn_c1c] using (nb090_compact_fv_empty_0354 A)

theorem nb090_compact_fv_empty_0355 (h : Var) : (nb090_alpha_dummy_484 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1229 (h : Var) : (nb090_alpha_dummy_484 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_484, fv_syn_c1c] using (nb090_compact_fv_empty_0355 h)

theorem nb090_compact_fv_empty_0356 (A : Class) : (nb090_alpha_dummy_479 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1230 (A : Class) : (nb090_alpha_dummy_479 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_479, fv_syn_c1c] using (nb090_compact_fv_empty_0356 A)

theorem nb090_compact_fv_empty_0357 (h : Var) : (nb090_alpha_dummy_480 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1231 (h : Var) : (nb090_alpha_dummy_480 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_480, fv_syn_c1c] using (nb090_compact_fv_empty_0357 h)

theorem nb090_compact_fv_empty_0358 (A : Class) : (nb090_alpha_dummy_475 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1232 (A : Class) : (nb090_alpha_dummy_475 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_475, fv_syn_c1c] using (nb090_compact_fv_empty_0358 A)

theorem nb090_compact_fv_empty_0359 (h : Var) : (nb090_alpha_dummy_477 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1233 (h : Var) : (nb090_alpha_dummy_477 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_477, fv_syn_c1c] using (nb090_compact_fv_empty_0359 h)

theorem nb090_compact_fv_empty_0360 (A : Class) : (nb090_alpha_dummy_476 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1234 (A : Class) : (nb090_alpha_dummy_476 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_476, fv_syn_c1c] using (nb090_compact_fv_empty_0360 A)

theorem nb090_compact_fv_empty_0361 (h : Var) : (nb090_alpha_dummy_478 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1235 (h : Var) : (nb090_alpha_dummy_478 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_478, fv_syn_c1c] using (nb090_compact_fv_empty_0361 h)

theorem nb090_compact_fv_empty_0362 (A : Class) : (nb090_alpha_dummy_468 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1236 (A : Class) : (nb090_alpha_dummy_468 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_468, fv_syn_c1c] using (nb090_compact_fv_empty_0362 A)

theorem nb090_compact_fv_empty_0363 (h : Var) : (nb090_alpha_dummy_470 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1237 (h : Var) : (nb090_alpha_dummy_470 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_470, fv_syn_c1c] using (nb090_compact_fv_empty_0363 h)

theorem nb090_compact_fv_empty_0364 (A : Class) : (nb090_alpha_dummy_467 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1238 (A : Class) : (nb090_alpha_dummy_467 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_467, fv_syn_c1c] using (nb090_compact_fv_empty_0364 A)

theorem nb090_compact_fv_empty_0365 (h : Var) : (nb090_alpha_dummy_469 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1239 (h : Var) : (nb090_alpha_dummy_469 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_469, fv_syn_c1c] using (nb090_compact_fv_empty_0365 h)

theorem nb090_compact_fv_empty_0366 (A : Class) : (nb090_alpha_dummy_473 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1240 (A : Class) : (nb090_alpha_dummy_473 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_473, fv_syn_c1c] using (nb090_compact_fv_empty_0366 A)

theorem nb090_compact_fv_empty_0367 (h : Var) : (nb090_alpha_dummy_474 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1241 (h : Var) : (nb090_alpha_dummy_474 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_474, fv_syn_c1c] using (nb090_compact_fv_empty_0367 h)

theorem nb090_compact_fv_empty_0368 (A : Class) : (nb090_alpha_dummy_471 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1242 (A : Class) : (nb090_alpha_dummy_471 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_471, fv_syn_c1c] using (nb090_compact_fv_empty_0368 A)

theorem nb090_compact_fv_empty_0369 (h : Var) : (nb090_alpha_dummy_472 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1243 (h : Var) : (nb090_alpha_dummy_472 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_472, fv_syn_c1c] using (nb090_compact_fv_empty_0369 h)

theorem nb090_compact_fv_empty_0370 (A : Class) : (nb090_alpha_dummy_425 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1244 (A : Class) : (nb090_alpha_dummy_425 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_425, fv_syn_c1c] using (nb090_compact_fv_empty_0370 A)

theorem nb090_compact_fv_empty_0371 (h : Var) : (nb090_alpha_dummy_428 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1245 (h : Var) : (nb090_alpha_dummy_428 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_428, fv_syn_c1c] using (nb090_compact_fv_empty_0371 h)

theorem nb090_compact_envfresh_0140 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_483 A), (nb090_alpha_dummy_486 h)), ((nb090_alpha_dummy_482 A), (nb090_alpha_dummy_485 h)), ((nb090_alpha_dummy_481 A), (nb090_alpha_dummy_484 h)), ((nb090_alpha_dummy_479 A), (nb090_alpha_dummy_480 h)), ((nb090_alpha_dummy_475 A), (nb090_alpha_dummy_477 h)), ((nb090_alpha_dummy_476 A), (nb090_alpha_dummy_478 h)), ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)), ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)), ((nb090_alpha_dummy_473 A), (nb090_alpha_dummy_474 h)), ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_483 A) (nb090_alpha_dummy_486 h) (nb090_wpp_notmem_1224 A) (nb090_wpp_notmem_1225 h) (TEnvFresh.consFresh (nb090_alpha_dummy_482 A) (nb090_alpha_dummy_485 h) (nb090_wpp_notmem_1226 A) (nb090_wpp_notmem_1227 h) (TEnvFresh.consFresh (nb090_alpha_dummy_481 A) (nb090_alpha_dummy_484 h) (nb090_wpp_notmem_1228 A) (nb090_wpp_notmem_1229 h) (TEnvFresh.consFresh (nb090_alpha_dummy_479 A) (nb090_alpha_dummy_480 h) (nb090_wpp_notmem_1230 A) (nb090_wpp_notmem_1231 h) (TEnvFresh.consFresh (nb090_alpha_dummy_475 A) (nb090_alpha_dummy_477 h) (nb090_wpp_notmem_1232 A) (nb090_wpp_notmem_1233 h) (TEnvFresh.consFresh (nb090_alpha_dummy_476 A) (nb090_alpha_dummy_478 h) (nb090_wpp_notmem_1234 A) (nb090_wpp_notmem_1235 h) (TEnvFresh.consFresh (nb090_alpha_dummy_468 A) (nb090_alpha_dummy_470 h) (nb090_wpp_notmem_1236 A) (nb090_wpp_notmem_1237 h) (TEnvFresh.consFresh (nb090_alpha_dummy_467 A) (nb090_alpha_dummy_469 h) (nb090_wpp_notmem_1238 A) (nb090_wpp_notmem_1239 h) (TEnvFresh.consFresh (nb090_alpha_dummy_473 A) (nb090_alpha_dummy_474 h) (nb090_wpp_notmem_1240 A) (nb090_wpp_notmem_1241 h) (TEnvFresh.consFresh (nb090_alpha_dummy_471 A) (nb090_alpha_dummy_472 h) (nb090_wpp_notmem_1242 A) (nb090_wpp_notmem_1243 h) (TEnvFresh.consFresh (nb090_alpha_dummy_425 A) (nb090_alpha_dummy_428 h) (nb090_wpp_notmem_1244 A) (nb090_wpp_notmem_1245 h) (TEnvFresh.consFresh (nb090_alpha_dummy_424 A) (nb090_alpha_dummy_427 h) (nb090_wpp_notmem_1122 A) (nb090_wpp_notmem_1123 h) (TEnvFresh.consFresh (nb090_alpha_dummy_423 A) (nb090_alpha_dummy_426 h) (nb090_wpp_notmem_1124 A) (nb090_wpp_notmem_1125 h) (TEnvFresh.consFresh (nb090_alpha_dummy_429 A) (nb090_alpha_dummy_430 h) (nb090_wpp_notmem_1126 A) (nb090_wpp_notmem_1127 h) (TEnvFresh.consFresh (nb090_alpha_dummy_421 A) (nb090_alpha_dummy_422 h) (nb090_wpp_notmem_1128 A) (nb090_wpp_notmem_1129 h) (TEnvFresh.consFresh (nb090_alpha_dummy_419 A) (nb090_alpha_dummy_420 h) (nb090_wpp_notmem_1130 A) (nb090_wpp_notmem_1131 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0142 A) (nb090_wpp_notmem_0143 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0020 A) (nb090_wpp_notmem_0021 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0022 A) (nb090_wpp_notmem_0023 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0024 A) (nb090_wpp_notmem_0025 v u A h) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))

noncomputable def nb090_wpp_refl_0140 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_483 A), (nb090_alpha_dummy_486 h)), ((nb090_alpha_dummy_482 A), (nb090_alpha_dummy_485 h)), ((nb090_alpha_dummy_481 A), (nb090_alpha_dummy_484 h)), ((nb090_alpha_dummy_479 A), (nb090_alpha_dummy_480 h)), ((nb090_alpha_dummy_475 A), (nb090_alpha_dummy_477 h)), ((nb090_alpha_dummy_476 A), (nb090_alpha_dummy_478 h)), ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)), ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)), ((nb090_alpha_dummy_473 A), (nb090_alpha_dummy_474 h)), ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0140 v u A h)

theorem nb090_wpp_notmem_1246 (A : Class) : (nb090_alpha_dummy_483 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_483, fv_syn_c0] using (nb090_compact_fv_empty_0350 A)

theorem nb090_wpp_notmem_1247 (h : Var) : (nb090_alpha_dummy_486 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_486, fv_syn_c0] using (nb090_compact_fv_empty_0351 h)

theorem nb090_wpp_notmem_1248 (A : Class) : (nb090_alpha_dummy_482 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_482, fv_syn_c0] using (nb090_compact_fv_empty_0352 A)

theorem nb090_wpp_notmem_1249 (h : Var) : (nb090_alpha_dummy_485 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_485, fv_syn_c0] using (nb090_compact_fv_empty_0353 h)

theorem nb090_wpp_notmem_1250 (A : Class) : (nb090_alpha_dummy_481 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_481, fv_syn_c0] using (nb090_compact_fv_empty_0354 A)

theorem nb090_wpp_notmem_1251 (h : Var) : (nb090_alpha_dummy_484 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_484, fv_syn_c0] using (nb090_compact_fv_empty_0355 h)

theorem nb090_wpp_notmem_1252 (A : Class) : (nb090_alpha_dummy_479 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_479, fv_syn_c0] using (nb090_compact_fv_empty_0356 A)

theorem nb090_wpp_notmem_1253 (h : Var) : (nb090_alpha_dummy_480 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_480, fv_syn_c0] using (nb090_compact_fv_empty_0357 h)

theorem nb090_wpp_notmem_1254 (A : Class) : (nb090_alpha_dummy_475 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_475, fv_syn_c0] using (nb090_compact_fv_empty_0358 A)

theorem nb090_wpp_notmem_1255 (h : Var) : (nb090_alpha_dummy_477 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_477, fv_syn_c0] using (nb090_compact_fv_empty_0359 h)

theorem nb090_wpp_notmem_1256 (A : Class) : (nb090_alpha_dummy_476 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_476, fv_syn_c0] using (nb090_compact_fv_empty_0360 A)

theorem nb090_wpp_notmem_1257 (h : Var) : (nb090_alpha_dummy_478 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_478, fv_syn_c0] using (nb090_compact_fv_empty_0361 h)

theorem nb090_wpp_notmem_1258 (A : Class) : (nb090_alpha_dummy_468 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_468, fv_syn_c0] using (nb090_compact_fv_empty_0362 A)

theorem nb090_wpp_notmem_1259 (h : Var) : (nb090_alpha_dummy_470 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_470, fv_syn_c0] using (nb090_compact_fv_empty_0363 h)

theorem nb090_wpp_notmem_1260 (A : Class) : (nb090_alpha_dummy_467 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_467, fv_syn_c0] using (nb090_compact_fv_empty_0364 A)

theorem nb090_wpp_notmem_1261 (h : Var) : (nb090_alpha_dummy_469 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_469, fv_syn_c0] using (nb090_compact_fv_empty_0365 h)

theorem nb090_wpp_notmem_1262 (A : Class) : (nb090_alpha_dummy_473 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_473, fv_syn_c0] using (nb090_compact_fv_empty_0366 A)

theorem nb090_wpp_notmem_1263 (h : Var) : (nb090_alpha_dummy_474 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_474, fv_syn_c0] using (nb090_compact_fv_empty_0367 h)

theorem nb090_wpp_notmem_1264 (A : Class) : (nb090_alpha_dummy_471 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_471, fv_syn_c0] using (nb090_compact_fv_empty_0368 A)

theorem nb090_wpp_notmem_1265 (h : Var) : (nb090_alpha_dummy_472 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_472, fv_syn_c0] using (nb090_compact_fv_empty_0369 h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
