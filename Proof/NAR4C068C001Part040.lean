import NAR4C068C001Part039

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

theorem nb068_compact_fv_empty_0329 (f : Var) : (nb068_alpha_dummy_418 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1071 (f : Var) : (nb068_alpha_dummy_418 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_418, fv_syn_c1c] using (nb068_compact_fv_empty_0329 f)

theorem nb068_compact_fv_empty_0330 : (nb068_alpha_dummy_408) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1072 : (nb068_alpha_dummy_408) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_408, fv_syn_c1c] using (nb068_compact_fv_empty_0330)

theorem nb068_compact_fv_empty_0331 (f : Var) : (nb068_alpha_dummy_410 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1073 (f : Var) : (nb068_alpha_dummy_410 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_410, fv_syn_c1c] using (nb068_compact_fv_empty_0331 f)

theorem nb068_compact_fv_empty_0332 : (nb068_alpha_dummy_407) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1074 : (nb068_alpha_dummy_407) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_407, fv_syn_c1c] using (nb068_compact_fv_empty_0332)

theorem nb068_compact_fv_empty_0333 (f : Var) : (nb068_alpha_dummy_409 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1075 (f : Var) : (nb068_alpha_dummy_409 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_409, fv_syn_c1c] using (nb068_compact_fv_empty_0333 f)

theorem nb068_compact_fv_empty_0334 : (nb068_alpha_dummy_411) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1076 : (nb068_alpha_dummy_411) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_411, fv_syn_c1c] using (nb068_compact_fv_empty_0334)

theorem nb068_compact_fv_empty_0335 (f : Var) : (nb068_alpha_dummy_412 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1077 (f : Var) : (nb068_alpha_dummy_412 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_412, fv_syn_c1c] using (nb068_compact_fv_empty_0335 f)

theorem nb068_compact_envfresh_0130 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_429), (nb068_alpha_dummy_432 f)), ((nb068_alpha_dummy_428), (nb068_alpha_dummy_431 f)), ((nb068_alpha_dummy_427), (nb068_alpha_dummy_430 f)), ((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)), ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)), ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_419), (nb068_alpha_dummy_420 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_429) (nb068_alpha_dummy_432 f) (nb068_wpp_notmem_1052) (nb068_wpp_notmem_1053 f) (TEnvFresh.consFresh (nb068_alpha_dummy_428) (nb068_alpha_dummy_431 f) (nb068_wpp_notmem_1054) (nb068_wpp_notmem_1055 f) (TEnvFresh.consFresh (nb068_alpha_dummy_427) (nb068_alpha_dummy_430 f) (nb068_wpp_notmem_1056) (nb068_wpp_notmem_1057 f) (TEnvFresh.consFresh (nb068_alpha_dummy_425) (nb068_alpha_dummy_426 f) (nb068_wpp_notmem_1058) (nb068_wpp_notmem_1059 f) (TEnvFresh.consFresh (nb068_alpha_dummy_421) (nb068_alpha_dummy_423 f) (nb068_wpp_notmem_1060) (nb068_wpp_notmem_1061 f) (TEnvFresh.consFresh (nb068_alpha_dummy_422) (nb068_alpha_dummy_424 f) (nb068_wpp_notmem_1062) (nb068_wpp_notmem_1063 f) (TEnvFresh.consFresh (nb068_alpha_dummy_414) (nb068_alpha_dummy_416 f) (nb068_wpp_notmem_1064) (nb068_wpp_notmem_1065 f) (TEnvFresh.consFresh (nb068_alpha_dummy_413) (nb068_alpha_dummy_415 f) (nb068_wpp_notmem_1066) (nb068_wpp_notmem_1067 f) (TEnvFresh.consFresh (nb068_alpha_dummy_419) (nb068_alpha_dummy_420 f) (nb068_wpp_notmem_1068) (nb068_wpp_notmem_1069 f) (TEnvFresh.consFresh (nb068_alpha_dummy_417) (nb068_alpha_dummy_418 f) (nb068_wpp_notmem_1070) (nb068_wpp_notmem_1071 f) (TEnvFresh.consFresh (nb068_alpha_dummy_408) (nb068_alpha_dummy_410 f) (nb068_wpp_notmem_1072) (nb068_wpp_notmem_1073 f) (TEnvFresh.consFresh (nb068_alpha_dummy_407) (nb068_alpha_dummy_409 f) (nb068_wpp_notmem_1074) (nb068_wpp_notmem_1075 f) (TEnvFresh.consFresh (nb068_alpha_dummy_411) (nb068_alpha_dummy_412 f) (nb068_wpp_notmem_1076) (nb068_wpp_notmem_1077 f) (TEnvFresh.consFresh (nb068_alpha_dummy_329) (nb068_alpha_dummy_332 f) (nb068_wpp_notmem_0982) (nb068_wpp_notmem_0983 f) (TEnvFresh.consFresh (nb068_alpha_dummy_328) (nb068_alpha_dummy_331 f) (nb068_wpp_notmem_0860) (nb068_wpp_notmem_0861 f) (TEnvFresh.consFresh (nb068_alpha_dummy_327) (nb068_alpha_dummy_330 f) (nb068_wpp_notmem_0862) (nb068_wpp_notmem_0863 f) (TEnvFresh.consFresh (nb068_alpha_dummy_333) (nb068_alpha_dummy_334 f) (nb068_wpp_notmem_0864) (nb068_wpp_notmem_0865 f) (TEnvFresh.consFresh (nb068_alpha_dummy_325) (nb068_alpha_dummy_326 f) (nb068_wpp_notmem_0866) (nb068_wpp_notmem_0867 f) (TEnvFresh.consFresh (nb068_alpha_dummy_323) (nb068_alpha_dummy_324 f) (nb068_wpp_notmem_0868) (nb068_wpp_notmem_0869 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0136) (nb068_wpp_notmem_0137 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0020) (nb068_wpp_notmem_0021 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0022) (nb068_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0024) (nb068_wpp_notmem_0025 x y f) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))))))

noncomputable def nb068_wpp_refl_0130 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_429), (nb068_alpha_dummy_432 f)), ((nb068_alpha_dummy_428), (nb068_alpha_dummy_431 f)), ((nb068_alpha_dummy_427), (nb068_alpha_dummy_430 f)), ((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)), ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)), ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_419), (nb068_alpha_dummy_420 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0130 x y f)

theorem nb068_wpp_notmem_1078 : (nb068_alpha_dummy_429) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_429, fv_syn_c0] using (nb068_compact_fv_empty_0310)

theorem nb068_wpp_notmem_1079 (f : Var) : (nb068_alpha_dummy_432 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_432, fv_syn_c0] using (nb068_compact_fv_empty_0311 f)

theorem nb068_wpp_notmem_1080 : (nb068_alpha_dummy_428) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_428, fv_syn_c0] using (nb068_compact_fv_empty_0312)

theorem nb068_wpp_notmem_1081 (f : Var) : (nb068_alpha_dummy_431 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_431, fv_syn_c0] using (nb068_compact_fv_empty_0313 f)

theorem nb068_wpp_notmem_1082 : (nb068_alpha_dummy_427) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_427, fv_syn_c0] using (nb068_compact_fv_empty_0314)

theorem nb068_wpp_notmem_1083 (f : Var) : (nb068_alpha_dummy_430 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_430, fv_syn_c0] using (nb068_compact_fv_empty_0315 f)

theorem nb068_wpp_notmem_1084 : (nb068_alpha_dummy_425) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_425, fv_syn_c0] using (nb068_compact_fv_empty_0316)

theorem nb068_wpp_notmem_1085 (f : Var) : (nb068_alpha_dummy_426 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_426, fv_syn_c0] using (nb068_compact_fv_empty_0317 f)

theorem nb068_wpp_notmem_1086 : (nb068_alpha_dummy_421) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_421, fv_syn_c0] using (nb068_compact_fv_empty_0318)

theorem nb068_wpp_notmem_1087 (f : Var) : (nb068_alpha_dummy_423 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_423, fv_syn_c0] using (nb068_compact_fv_empty_0319 f)

theorem nb068_wpp_notmem_1088 : (nb068_alpha_dummy_422) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_422, fv_syn_c0] using (nb068_compact_fv_empty_0320)

theorem nb068_wpp_notmem_1089 (f : Var) : (nb068_alpha_dummy_424 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_424, fv_syn_c0] using (nb068_compact_fv_empty_0321 f)

theorem nb068_wpp_notmem_1090 : (nb068_alpha_dummy_414) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_414, fv_syn_c0] using (nb068_compact_fv_empty_0322)

theorem nb068_wpp_notmem_1091 (f : Var) : (nb068_alpha_dummy_416 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_416, fv_syn_c0] using (nb068_compact_fv_empty_0323 f)

theorem nb068_wpp_notmem_1092 : (nb068_alpha_dummy_413) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_413, fv_syn_c0] using (nb068_compact_fv_empty_0324)

theorem nb068_wpp_notmem_1093 (f : Var) : (nb068_alpha_dummy_415 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_415, fv_syn_c0] using (nb068_compact_fv_empty_0325 f)

theorem nb068_wpp_notmem_1094 : (nb068_alpha_dummy_419) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_419, fv_syn_c0] using (nb068_compact_fv_empty_0326)

theorem nb068_wpp_notmem_1095 (f : Var) : (nb068_alpha_dummy_420 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_420, fv_syn_c0] using (nb068_compact_fv_empty_0327 f)

theorem nb068_wpp_notmem_1096 : (nb068_alpha_dummy_417) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_417, fv_syn_c0] using (nb068_compact_fv_empty_0328)

theorem nb068_wpp_notmem_1097 (f : Var) : (nb068_alpha_dummy_418 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_418, fv_syn_c0] using (nb068_compact_fv_empty_0329 f)

theorem nb068_wpp_notmem_1098 : (nb068_alpha_dummy_408) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_408, fv_syn_c0] using (nb068_compact_fv_empty_0330)

theorem nb068_wpp_notmem_1099 (f : Var) : (nb068_alpha_dummy_410 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_410, fv_syn_c0] using (nb068_compact_fv_empty_0331 f)

theorem nb068_wpp_notmem_1100 : (nb068_alpha_dummy_407) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_407, fv_syn_c0] using (nb068_compact_fv_empty_0332)

theorem nb068_wpp_notmem_1101 (f : Var) : (nb068_alpha_dummy_409 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_409, fv_syn_c0] using (nb068_compact_fv_empty_0333 f)

theorem nb068_wpp_notmem_1102 : (nb068_alpha_dummy_411) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_411, fv_syn_c0] using (nb068_compact_fv_empty_0334)

theorem nb068_wpp_notmem_1103 (f : Var) : (nb068_alpha_dummy_412 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_412, fv_syn_c0] using (nb068_compact_fv_empty_0335 f)

theorem nb068_compact_envfresh_0131 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_429), (nb068_alpha_dummy_432 f)), ((nb068_alpha_dummy_428), (nb068_alpha_dummy_431 f)), ((nb068_alpha_dummy_427), (nb068_alpha_dummy_430 f)), ((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)), ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)), ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_419), (nb068_alpha_dummy_420 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_429) (nb068_alpha_dummy_432 f) (nb068_wpp_notmem_1078) (nb068_wpp_notmem_1079 f) (TEnvFresh.consFresh (nb068_alpha_dummy_428) (nb068_alpha_dummy_431 f) (nb068_wpp_notmem_1080) (nb068_wpp_notmem_1081 f) (TEnvFresh.consFresh (nb068_alpha_dummy_427) (nb068_alpha_dummy_430 f) (nb068_wpp_notmem_1082) (nb068_wpp_notmem_1083 f) (TEnvFresh.consFresh (nb068_alpha_dummy_425) (nb068_alpha_dummy_426 f) (nb068_wpp_notmem_1084) (nb068_wpp_notmem_1085 f) (TEnvFresh.consFresh (nb068_alpha_dummy_421) (nb068_alpha_dummy_423 f) (nb068_wpp_notmem_1086) (nb068_wpp_notmem_1087 f) (TEnvFresh.consFresh (nb068_alpha_dummy_422) (nb068_alpha_dummy_424 f) (nb068_wpp_notmem_1088) (nb068_wpp_notmem_1089 f) (TEnvFresh.consFresh (nb068_alpha_dummy_414) (nb068_alpha_dummy_416 f) (nb068_wpp_notmem_1090) (nb068_wpp_notmem_1091 f) (TEnvFresh.consFresh (nb068_alpha_dummy_413) (nb068_alpha_dummy_415 f) (nb068_wpp_notmem_1092) (nb068_wpp_notmem_1093 f) (TEnvFresh.consFresh (nb068_alpha_dummy_419) (nb068_alpha_dummy_420 f) (nb068_wpp_notmem_1094) (nb068_wpp_notmem_1095 f) (TEnvFresh.consFresh (nb068_alpha_dummy_417) (nb068_alpha_dummy_418 f) (nb068_wpp_notmem_1096) (nb068_wpp_notmem_1097 f) (TEnvFresh.consFresh (nb068_alpha_dummy_408) (nb068_alpha_dummy_410 f) (nb068_wpp_notmem_1098) (nb068_wpp_notmem_1099 f) (TEnvFresh.consFresh (nb068_alpha_dummy_407) (nb068_alpha_dummy_409 f) (nb068_wpp_notmem_1100) (nb068_wpp_notmem_1101 f) (TEnvFresh.consFresh (nb068_alpha_dummy_411) (nb068_alpha_dummy_412 f) (nb068_wpp_notmem_1102) (nb068_wpp_notmem_1103 f) (TEnvFresh.consFresh (nb068_alpha_dummy_329) (nb068_alpha_dummy_332 f) (nb068_wpp_notmem_1004) (nb068_wpp_notmem_1005 f) (TEnvFresh.consFresh (nb068_alpha_dummy_328) (nb068_alpha_dummy_331 f) (nb068_wpp_notmem_0890) (nb068_wpp_notmem_0891 f) (TEnvFresh.consFresh (nb068_alpha_dummy_327) (nb068_alpha_dummy_330 f) (nb068_wpp_notmem_0892) (nb068_wpp_notmem_0893 f) (TEnvFresh.consFresh (nb068_alpha_dummy_333) (nb068_alpha_dummy_334 f) (nb068_wpp_notmem_0894) (nb068_wpp_notmem_0895 f) (TEnvFresh.consFresh (nb068_alpha_dummy_325) (nb068_alpha_dummy_326 f) (nb068_wpp_notmem_0896) (nb068_wpp_notmem_0897 f) (TEnvFresh.consFresh (nb068_alpha_dummy_323) (nb068_alpha_dummy_324 f) (nb068_wpp_notmem_0898) (nb068_wpp_notmem_0899 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0168) (nb068_wpp_notmem_0169 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0046) (nb068_wpp_notmem_0047 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0048) (nb068_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0050) (nb068_wpp_notmem_0051 x y f) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))))))

noncomputable def nb068_wpp_refl_0131 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_429), (nb068_alpha_dummy_432 f)), ((nb068_alpha_dummy_428), (nb068_alpha_dummy_431 f)), ((nb068_alpha_dummy_427), (nb068_alpha_dummy_430 f)), ((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)), ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)), ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_419), (nb068_alpha_dummy_420 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0131 x y f)

noncomputable def nb068_split_alpha_0099 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_429), (nb068_alpha_dummy_432 f)), ((nb068_alpha_dummy_428), (nb068_alpha_dummy_431 f)), ((nb068_alpha_dummy_427), (nb068_alpha_dummy_430 f)), ((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)), ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)), ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_419), (nb068_alpha_dummy_420 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_428)) (Class.cv (nb068_alpha_dummy_429))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_427)) (syn_cun (Class.cv (nb068_alpha_dummy_428)) (Class.cv (nb068_alpha_dummy_429)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_431 f)) (Class.cv (nb068_alpha_dummy_432 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_430 f)) (syn_cun (Class.cv (nb068_alpha_dummy_431 f)) (Class.cv (nb068_alpha_dummy_432 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0438) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0439 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0436) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0437 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0442) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0443 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0440) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0441 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0438) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0439 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0436) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0437 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0442) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0443 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0440) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0441 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_429), (nb068_alpha_dummy_432 f)), ((nb068_alpha_dummy_428), (nb068_alpha_dummy_431 f)), ((nb068_alpha_dummy_427), (nb068_alpha_dummy_430 f)), ((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)), ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)), ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_419), (nb068_alpha_dummy_420 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c0) (nb068_wpp_refl_0131 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0446) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0447 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0444) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0445 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0446) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0447 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0444) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0445 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0450) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0451 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0448) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0449 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0450) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0451 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0448) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0449 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb068_wpp_notmem_1104 : (nb068_alpha_dummy_425) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_425, fv_syn_cnnc] using (nb068_compact_fv_empty_0316)

theorem nb068_wpp_notmem_1105 (f : Var) : (nb068_alpha_dummy_426 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_426, fv_syn_cnnc] using (nb068_compact_fv_empty_0317 f)

theorem nb068_wpp_notmem_1106 : (nb068_alpha_dummy_421) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_421, fv_syn_cnnc] using (nb068_compact_fv_empty_0318)

theorem nb068_wpp_notmem_1107 (f : Var) : (nb068_alpha_dummy_423 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_423, fv_syn_cnnc] using (nb068_compact_fv_empty_0319 f)

theorem nb068_wpp_notmem_1108 : (nb068_alpha_dummy_422) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_422, fv_syn_cnnc] using (nb068_compact_fv_empty_0320)

theorem nb068_wpp_notmem_1109 (f : Var) : (nb068_alpha_dummy_424 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_424, fv_syn_cnnc] using (nb068_compact_fv_empty_0321 f)

theorem nb068_wpp_notmem_1110 : (nb068_alpha_dummy_414) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_414, fv_syn_cnnc] using (nb068_compact_fv_empty_0322)

theorem nb068_wpp_notmem_1111 (f : Var) : (nb068_alpha_dummy_416 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_416, fv_syn_cnnc] using (nb068_compact_fv_empty_0323 f)

theorem nb068_wpp_notmem_1112 : (nb068_alpha_dummy_413) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_413, fv_syn_cnnc] using (nb068_compact_fv_empty_0324)

theorem nb068_wpp_notmem_1113 (f : Var) : (nb068_alpha_dummy_415 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_415, fv_syn_cnnc] using (nb068_compact_fv_empty_0325 f)

theorem nb068_wpp_notmem_1114 : (nb068_alpha_dummy_419) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_419, fv_syn_cnnc] using (nb068_compact_fv_empty_0326)

theorem nb068_wpp_notmem_1115 (f : Var) : (nb068_alpha_dummy_420 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_420, fv_syn_cnnc] using (nb068_compact_fv_empty_0327 f)

theorem nb068_wpp_notmem_1116 : (nb068_alpha_dummy_417) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_417, fv_syn_cnnc] using (nb068_compact_fv_empty_0328)

theorem nb068_wpp_notmem_1117 (f : Var) : (nb068_alpha_dummy_418 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_418, fv_syn_cnnc] using (nb068_compact_fv_empty_0329 f)

theorem nb068_wpp_notmem_1118 : (nb068_alpha_dummy_408) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_408, fv_syn_cnnc] using (nb068_compact_fv_empty_0330)

theorem nb068_wpp_notmem_1119 (f : Var) : (nb068_alpha_dummy_410 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_410, fv_syn_cnnc] using (nb068_compact_fv_empty_0331 f)

theorem nb068_wpp_notmem_1120 : (nb068_alpha_dummy_407) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_407, fv_syn_cnnc] using (nb068_compact_fv_empty_0332)

theorem nb068_wpp_notmem_1121 (f : Var) : (nb068_alpha_dummy_409 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_409, fv_syn_cnnc] using (nb068_compact_fv_empty_0333 f)

theorem nb068_wpp_notmem_1122 : (nb068_alpha_dummy_411) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_411, fv_syn_cnnc] using (nb068_compact_fv_empty_0334)

theorem nb068_wpp_notmem_1123 (f : Var) : (nb068_alpha_dummy_412 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_412, fv_syn_cnnc] using (nb068_compact_fv_empty_0335 f)

theorem nb068_compact_envfresh_0132 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)), ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)), ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_419), (nb068_alpha_dummy_420 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_425) (nb068_alpha_dummy_426 f) (nb068_wpp_notmem_1104) (nb068_wpp_notmem_1105 f) (TEnvFresh.consFresh (nb068_alpha_dummy_421) (nb068_alpha_dummy_423 f) (nb068_wpp_notmem_1106) (nb068_wpp_notmem_1107 f) (TEnvFresh.consFresh (nb068_alpha_dummy_422) (nb068_alpha_dummy_424 f) (nb068_wpp_notmem_1108) (nb068_wpp_notmem_1109 f) (TEnvFresh.consFresh (nb068_alpha_dummy_414) (nb068_alpha_dummy_416 f) (nb068_wpp_notmem_1110) (nb068_wpp_notmem_1111 f) (TEnvFresh.consFresh (nb068_alpha_dummy_413) (nb068_alpha_dummy_415 f) (nb068_wpp_notmem_1112) (nb068_wpp_notmem_1113 f) (TEnvFresh.consFresh (nb068_alpha_dummy_419) (nb068_alpha_dummy_420 f) (nb068_wpp_notmem_1114) (nb068_wpp_notmem_1115 f) (TEnvFresh.consFresh (nb068_alpha_dummy_417) (nb068_alpha_dummy_418 f) (nb068_wpp_notmem_1116) (nb068_wpp_notmem_1117 f) (TEnvFresh.consFresh (nb068_alpha_dummy_408) (nb068_alpha_dummy_410 f) (nb068_wpp_notmem_1118) (nb068_wpp_notmem_1119 f) (TEnvFresh.consFresh (nb068_alpha_dummy_407) (nb068_alpha_dummy_409 f) (nb068_wpp_notmem_1120) (nb068_wpp_notmem_1121 f) (TEnvFresh.consFresh (nb068_alpha_dummy_411) (nb068_alpha_dummy_412 f) (nb068_wpp_notmem_1122) (nb068_wpp_notmem_1123 f) (TEnvFresh.consFresh (nb068_alpha_dummy_329) (nb068_alpha_dummy_332 f) (nb068_wpp_notmem_1020) (nb068_wpp_notmem_1021 f) (TEnvFresh.consFresh (nb068_alpha_dummy_328) (nb068_alpha_dummy_331 f) (nb068_wpp_notmem_0914) (nb068_wpp_notmem_0915 f) (TEnvFresh.consFresh (nb068_alpha_dummy_327) (nb068_alpha_dummy_330 f) (nb068_wpp_notmem_0916) (nb068_wpp_notmem_0917 f) (TEnvFresh.consFresh (nb068_alpha_dummy_333) (nb068_alpha_dummy_334 f) (nb068_wpp_notmem_0918) (nb068_wpp_notmem_0919 f) (TEnvFresh.consFresh (nb068_alpha_dummy_325) (nb068_alpha_dummy_326 f) (nb068_wpp_notmem_0920) (nb068_wpp_notmem_0921 f) (TEnvFresh.consFresh (nb068_alpha_dummy_323) (nb068_alpha_dummy_324 f) (nb068_wpp_notmem_0922) (nb068_wpp_notmem_0923 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0194) (nb068_wpp_notmem_0195 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0066) (nb068_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0068) (nb068_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0070) (nb068_wpp_notmem_0071 x y f) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))))))

noncomputable def nb068_wpp_refl_0132 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)), ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)), ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_419), (nb068_alpha_dummy_420 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0132 x y f)

noncomputable def nb068_split_alpha_0100 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)), ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_419), (nb068_alpha_dummy_420 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.classEq (Class.cv (nb068_alpha_dummy_422)) (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_421)) (syn_cnnc)) (syn_cplc (Class.cv (nb068_alpha_dummy_421)) (syn_c1c)) (Class.cv (nb068_alpha_dummy_421)))) (Wff.classEq (Class.cv (nb068_alpha_dummy_424 f)) (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_423 f)) (syn_cnnc)) (syn_cplc (Class.cv (nb068_alpha_dummy_423 f)) (syn_c1c)) (Class.cv (nb068_alpha_dummy_423 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_414))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_416 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0434) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0435 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0434) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0435 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0432) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0433 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_429), (nb068_alpha_dummy_432 f)), ((nb068_alpha_dummy_428), (nb068_alpha_dummy_431 f)), ((nb068_alpha_dummy_427), (nb068_alpha_dummy_430 f)), ((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)), ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)), ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_419), (nb068_alpha_dummy_420 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c1c) (nb068_wpp_refl_0130 x y f))) (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0099 x y f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0432) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0433 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)), ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)), ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_419), (nb068_alpha_dummy_420 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0132 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0432) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0433 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0432) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0433 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)), ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)), ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_419), (nb068_alpha_dummy_420 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0132 x y f))))))))))

theorem nb068_compact_fv_empty_0336 : (nb068_alpha_dummy_447) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1124 : (nb068_alpha_dummy_447) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_447, fv_syn_c1c] using (nb068_compact_fv_empty_0336)

theorem nb068_compact_fv_empty_0337 (f : Var) : (nb068_alpha_dummy_448 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1125 (f : Var) : (nb068_alpha_dummy_448 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_448, fv_syn_c1c] using (nb068_compact_fv_empty_0337 f)

theorem nb068_compact_fv_empty_0338 : (nb068_alpha_dummy_445) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1126 : (nb068_alpha_dummy_445) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_445, fv_syn_c1c] using (nb068_compact_fv_empty_0338)

theorem nb068_compact_fv_empty_0339 (f : Var) : (nb068_alpha_dummy_446 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1127 (f : Var) : (nb068_alpha_dummy_446 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_446, fv_syn_c1c] using (nb068_compact_fv_empty_0339 f)

theorem nb068_compact_fv_empty_0340 : (nb068_alpha_dummy_443) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1128 : (nb068_alpha_dummy_443) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_443, fv_syn_c1c] using (nb068_compact_fv_empty_0340)

theorem nb068_compact_fv_empty_0341 (f : Var) : (nb068_alpha_dummy_444 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1129 (f : Var) : (nb068_alpha_dummy_444 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_444, fv_syn_c1c] using (nb068_compact_fv_empty_0341 f)

theorem nb068_compact_envfresh_0133 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_429), (nb068_alpha_dummy_432 f)), ((nb068_alpha_dummy_428), (nb068_alpha_dummy_431 f)), ((nb068_alpha_dummy_427), (nb068_alpha_dummy_430 f)), ((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)), ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)), ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)), ((nb068_alpha_dummy_447), (nb068_alpha_dummy_448 f)), ((nb068_alpha_dummy_445), (nb068_alpha_dummy_446 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_429) (nb068_alpha_dummy_432 f) (nb068_wpp_notmem_1052) (nb068_wpp_notmem_1053 f) (TEnvFresh.consFresh (nb068_alpha_dummy_428) (nb068_alpha_dummy_431 f) (nb068_wpp_notmem_1054) (nb068_wpp_notmem_1055 f) (TEnvFresh.consFresh (nb068_alpha_dummy_427) (nb068_alpha_dummy_430 f) (nb068_wpp_notmem_1056) (nb068_wpp_notmem_1057 f) (TEnvFresh.consFresh (nb068_alpha_dummy_425) (nb068_alpha_dummy_426 f) (nb068_wpp_notmem_1058) (nb068_wpp_notmem_1059 f) (TEnvFresh.consFresh (nb068_alpha_dummy_421) (nb068_alpha_dummy_423 f) (nb068_wpp_notmem_1060) (nb068_wpp_notmem_1061 f) (TEnvFresh.consFresh (nb068_alpha_dummy_422) (nb068_alpha_dummy_424 f) (nb068_wpp_notmem_1062) (nb068_wpp_notmem_1063 f) (TEnvFresh.consFresh (nb068_alpha_dummy_447) (nb068_alpha_dummy_448 f) (nb068_wpp_notmem_1124) (nb068_wpp_notmem_1125 f) (TEnvFresh.consFresh (nb068_alpha_dummy_445) (nb068_alpha_dummy_446 f) (nb068_wpp_notmem_1126) (nb068_wpp_notmem_1127 f) (TEnvFresh.consFresh (nb068_alpha_dummy_414) (nb068_alpha_dummy_416 f) (nb068_wpp_notmem_1064) (nb068_wpp_notmem_1065 f) (TEnvFresh.consFresh (nb068_alpha_dummy_413) (nb068_alpha_dummy_415 f) (nb068_wpp_notmem_1066) (nb068_wpp_notmem_1067 f) (TEnvFresh.consFresh (nb068_alpha_dummy_443) (nb068_alpha_dummy_444 f) (nb068_wpp_notmem_1128) (nb068_wpp_notmem_1129 f) (TEnvFresh.consFresh (nb068_alpha_dummy_417) (nb068_alpha_dummy_418 f) (nb068_wpp_notmem_1070) (nb068_wpp_notmem_1071 f) (TEnvFresh.consFresh (nb068_alpha_dummy_408) (nb068_alpha_dummy_410 f) (nb068_wpp_notmem_1072) (nb068_wpp_notmem_1073 f) (TEnvFresh.consFresh (nb068_alpha_dummy_407) (nb068_alpha_dummy_409 f) (nb068_wpp_notmem_1074) (nb068_wpp_notmem_1075 f) (TEnvFresh.consFresh (nb068_alpha_dummy_411) (nb068_alpha_dummy_412 f) (nb068_wpp_notmem_1076) (nb068_wpp_notmem_1077 f) (TEnvFresh.consFresh (nb068_alpha_dummy_329) (nb068_alpha_dummy_332 f) (nb068_wpp_notmem_0982) (nb068_wpp_notmem_0983 f) (TEnvFresh.consFresh (nb068_alpha_dummy_328) (nb068_alpha_dummy_331 f) (nb068_wpp_notmem_0860) (nb068_wpp_notmem_0861 f) (TEnvFresh.consFresh (nb068_alpha_dummy_327) (nb068_alpha_dummy_330 f) (nb068_wpp_notmem_0862) (nb068_wpp_notmem_0863 f) (TEnvFresh.consFresh (nb068_alpha_dummy_333) (nb068_alpha_dummy_334 f) (nb068_wpp_notmem_0864) (nb068_wpp_notmem_0865 f) (TEnvFresh.consFresh (nb068_alpha_dummy_325) (nb068_alpha_dummy_326 f) (nb068_wpp_notmem_0866) (nb068_wpp_notmem_0867 f) (TEnvFresh.consFresh (nb068_alpha_dummy_323) (nb068_alpha_dummy_324 f) (nb068_wpp_notmem_0868) (nb068_wpp_notmem_0869 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0136) (nb068_wpp_notmem_0137 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0020) (nb068_wpp_notmem_0021 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0022) (nb068_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0024) (nb068_wpp_notmem_0025 x y f) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))))))))

noncomputable def nb068_wpp_refl_0133 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_429), (nb068_alpha_dummy_432 f)), ((nb068_alpha_dummy_428), (nb068_alpha_dummy_431 f)), ((nb068_alpha_dummy_427), (nb068_alpha_dummy_430 f)), ((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)), ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)), ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)), ((nb068_alpha_dummy_447), (nb068_alpha_dummy_448 f)), ((nb068_alpha_dummy_445), (nb068_alpha_dummy_446 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0133 x y f)

theorem nb068_wpp_notmem_1130 : (nb068_alpha_dummy_447) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_447, fv_syn_c0] using (nb068_compact_fv_empty_0336)

theorem nb068_wpp_notmem_1131 (f : Var) : (nb068_alpha_dummy_448 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_448, fv_syn_c0] using (nb068_compact_fv_empty_0337 f)

theorem nb068_wpp_notmem_1132 : (nb068_alpha_dummy_445) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_445, fv_syn_c0] using (nb068_compact_fv_empty_0338)

theorem nb068_wpp_notmem_1133 (f : Var) : (nb068_alpha_dummy_446 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_446, fv_syn_c0] using (nb068_compact_fv_empty_0339 f)

theorem nb068_wpp_notmem_1134 : (nb068_alpha_dummy_443) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_443, fv_syn_c0] using (nb068_compact_fv_empty_0340)

theorem nb068_wpp_notmem_1135 (f : Var) : (nb068_alpha_dummy_444 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_444, fv_syn_c0] using (nb068_compact_fv_empty_0341 f)

theorem nb068_compact_envfresh_0134 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_429), (nb068_alpha_dummy_432 f)), ((nb068_alpha_dummy_428), (nb068_alpha_dummy_431 f)), ((nb068_alpha_dummy_427), (nb068_alpha_dummy_430 f)), ((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)), ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)), ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)), ((nb068_alpha_dummy_447), (nb068_alpha_dummy_448 f)), ((nb068_alpha_dummy_445), (nb068_alpha_dummy_446 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_429) (nb068_alpha_dummy_432 f) (nb068_wpp_notmem_1078) (nb068_wpp_notmem_1079 f) (TEnvFresh.consFresh (nb068_alpha_dummy_428) (nb068_alpha_dummy_431 f) (nb068_wpp_notmem_1080) (nb068_wpp_notmem_1081 f) (TEnvFresh.consFresh (nb068_alpha_dummy_427) (nb068_alpha_dummy_430 f) (nb068_wpp_notmem_1082) (nb068_wpp_notmem_1083 f) (TEnvFresh.consFresh (nb068_alpha_dummy_425) (nb068_alpha_dummy_426 f) (nb068_wpp_notmem_1084) (nb068_wpp_notmem_1085 f) (TEnvFresh.consFresh (nb068_alpha_dummy_421) (nb068_alpha_dummy_423 f) (nb068_wpp_notmem_1086) (nb068_wpp_notmem_1087 f) (TEnvFresh.consFresh (nb068_alpha_dummy_422) (nb068_alpha_dummy_424 f) (nb068_wpp_notmem_1088) (nb068_wpp_notmem_1089 f) (TEnvFresh.consFresh (nb068_alpha_dummy_447) (nb068_alpha_dummy_448 f) (nb068_wpp_notmem_1130) (nb068_wpp_notmem_1131 f) (TEnvFresh.consFresh (nb068_alpha_dummy_445) (nb068_alpha_dummy_446 f) (nb068_wpp_notmem_1132) (nb068_wpp_notmem_1133 f) (TEnvFresh.consFresh (nb068_alpha_dummy_414) (nb068_alpha_dummy_416 f) (nb068_wpp_notmem_1090) (nb068_wpp_notmem_1091 f) (TEnvFresh.consFresh (nb068_alpha_dummy_413) (nb068_alpha_dummy_415 f) (nb068_wpp_notmem_1092) (nb068_wpp_notmem_1093 f) (TEnvFresh.consFresh (nb068_alpha_dummy_443) (nb068_alpha_dummy_444 f) (nb068_wpp_notmem_1134) (nb068_wpp_notmem_1135 f) (TEnvFresh.consFresh (nb068_alpha_dummy_417) (nb068_alpha_dummy_418 f) (nb068_wpp_notmem_1096) (nb068_wpp_notmem_1097 f) (TEnvFresh.consFresh (nb068_alpha_dummy_408) (nb068_alpha_dummy_410 f) (nb068_wpp_notmem_1098) (nb068_wpp_notmem_1099 f) (TEnvFresh.consFresh (nb068_alpha_dummy_407) (nb068_alpha_dummy_409 f) (nb068_wpp_notmem_1100) (nb068_wpp_notmem_1101 f) (TEnvFresh.consFresh (nb068_alpha_dummy_411) (nb068_alpha_dummy_412 f) (nb068_wpp_notmem_1102) (nb068_wpp_notmem_1103 f) (TEnvFresh.consFresh (nb068_alpha_dummy_329) (nb068_alpha_dummy_332 f) (nb068_wpp_notmem_1004) (nb068_wpp_notmem_1005 f) (TEnvFresh.consFresh (nb068_alpha_dummy_328) (nb068_alpha_dummy_331 f) (nb068_wpp_notmem_0890) (nb068_wpp_notmem_0891 f) (TEnvFresh.consFresh (nb068_alpha_dummy_327) (nb068_alpha_dummy_330 f) (nb068_wpp_notmem_0892) (nb068_wpp_notmem_0893 f) (TEnvFresh.consFresh (nb068_alpha_dummy_333) (nb068_alpha_dummy_334 f) (nb068_wpp_notmem_0894) (nb068_wpp_notmem_0895 f) (TEnvFresh.consFresh (nb068_alpha_dummy_325) (nb068_alpha_dummy_326 f) (nb068_wpp_notmem_0896) (nb068_wpp_notmem_0897 f) (TEnvFresh.consFresh (nb068_alpha_dummy_323) (nb068_alpha_dummy_324 f) (nb068_wpp_notmem_0898) (nb068_wpp_notmem_0899 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0168) (nb068_wpp_notmem_0169 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0046) (nb068_wpp_notmem_0047 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0048) (nb068_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0050) (nb068_wpp_notmem_0051 x y f) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))))))))

noncomputable def nb068_wpp_refl_0134 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_429), (nb068_alpha_dummy_432 f)), ((nb068_alpha_dummy_428), (nb068_alpha_dummy_431 f)), ((nb068_alpha_dummy_427), (nb068_alpha_dummy_430 f)), ((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)), ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)), ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)), ((nb068_alpha_dummy_447), (nb068_alpha_dummy_448 f)), ((nb068_alpha_dummy_445), (nb068_alpha_dummy_446 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0134 x y f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
