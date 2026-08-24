import NAR4C078C001Part165

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

theorem nb078_wpp_notmem_3058 : (nb078_alpha_dummy_1222) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0914)

theorem nb078_compact_fv_empty_0915 (h : Var) : (nb078_alpha_dummy_1225 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_3059 (h : Var) : (nb078_alpha_dummy_1225 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0915 h)

theorem nb078_compact_fv_empty_0916 : (nb078_alpha_dummy_1221) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_3060 : (nb078_alpha_dummy_1221) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0916)

theorem nb078_compact_fv_empty_0917 (h : Var) : (nb078_alpha_dummy_1224 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_3061 (h : Var) : (nb078_alpha_dummy_1224 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0917 h)

theorem nb078_compact_fv_empty_0918 : (nb078_alpha_dummy_1219) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_3062 : (nb078_alpha_dummy_1219) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0918)

theorem nb078_compact_fv_empty_0919 (h : Var) : (nb078_alpha_dummy_1220 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_3063 (h : Var) : (nb078_alpha_dummy_1220 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0919 h)

theorem nb078_compact_fv_empty_0920 : (nb078_alpha_dummy_1215) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_3064 : (nb078_alpha_dummy_1215) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0920)

theorem nb078_compact_fv_empty_0921 (h : Var) : (nb078_alpha_dummy_1217 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_3065 (h : Var) : (nb078_alpha_dummy_1217 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0921 h)

theorem nb078_compact_fv_empty_0922 : (nb078_alpha_dummy_1216) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_3066 : (nb078_alpha_dummy_1216) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0922)

theorem nb078_compact_fv_empty_0923 (h : Var) : (nb078_alpha_dummy_1218 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_3067 (h : Var) : (nb078_alpha_dummy_1218 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0923 h)

theorem nb078_compact_fv_empty_0924 : (nb078_alpha_dummy_1208) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_3068 : (nb078_alpha_dummy_1208) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0924)

theorem nb078_compact_fv_empty_0925 (h : Var) : (nb078_alpha_dummy_1210 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_3069 (h : Var) : (nb078_alpha_dummy_1210 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0925 h)

theorem nb078_compact_fv_empty_0926 : (nb078_alpha_dummy_1207) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_3070 : (nb078_alpha_dummy_1207) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0926)

theorem nb078_compact_fv_empty_0927 (h : Var) : (nb078_alpha_dummy_1209 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_3071 (h : Var) : (nb078_alpha_dummy_1209 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0927 h)

theorem nb078_compact_fv_empty_0928 : (nb078_alpha_dummy_1213) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_3072 : (nb078_alpha_dummy_1213) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0928)

theorem nb078_compact_fv_empty_0929 (h : Var) : (nb078_alpha_dummy_1214 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_3073 (h : Var) : (nb078_alpha_dummy_1214 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0929 h)

theorem nb078_compact_fv_empty_0930 : (nb078_alpha_dummy_1211) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_3074 : (nb078_alpha_dummy_1211) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0930)

theorem nb078_compact_fv_empty_0931 (h : Var) : (nb078_alpha_dummy_1212 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_3075 (h : Var) : (nb078_alpha_dummy_1212 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0931 h)

theorem nb078_compact_envfresh_0488 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_1223), (nb078_alpha_dummy_1226 h)), ((nb078_alpha_dummy_1222), (nb078_alpha_dummy_1225 h)), ((nb078_alpha_dummy_1221), (nb078_alpha_dummy_1224 h)), ((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)), ((nb078_alpha_dummy_1215), (nb078_alpha_dummy_1217 h)), ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)), ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)), ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)), ((nb078_alpha_dummy_1213), (nb078_alpha_dummy_1214 h)), ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_1223) (nb078_alpha_dummy_1226 h) (nb078_wpp_notmem_3056) (nb078_wpp_notmem_3057 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1222) (nb078_alpha_dummy_1225 h) (nb078_wpp_notmem_3058) (nb078_wpp_notmem_3059 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1221) (nb078_alpha_dummy_1224 h) (nb078_wpp_notmem_3060) (nb078_wpp_notmem_3061 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1219) (nb078_alpha_dummy_1220 h) (nb078_wpp_notmem_3062) (nb078_wpp_notmem_3063 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1215) (nb078_alpha_dummy_1217 h) (nb078_wpp_notmem_3064) (nb078_wpp_notmem_3065 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1216) (nb078_alpha_dummy_1218 h) (nb078_wpp_notmem_3066) (nb078_wpp_notmem_3067 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1208) (nb078_alpha_dummy_1210 h) (nb078_wpp_notmem_3068) (nb078_wpp_notmem_3069 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1207) (nb078_alpha_dummy_1209 h) (nb078_wpp_notmem_3070) (nb078_wpp_notmem_3071 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1213) (nb078_alpha_dummy_1214 h) (nb078_wpp_notmem_3072) (nb078_wpp_notmem_3073 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1211) (nb078_alpha_dummy_1212 h) (nb078_wpp_notmem_3074) (nb078_wpp_notmem_3075 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1051) (nb078_alpha_dummy_1054 h) (nb078_wpp_notmem_2798) (nb078_wpp_notmem_2799 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1050) (nb078_alpha_dummy_1053 h) (nb078_wpp_notmem_2676) (nb078_wpp_notmem_2677 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1049) (nb078_alpha_dummy_1052 h) (nb078_wpp_notmem_2678) (nb078_wpp_notmem_2679 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1055) (nb078_alpha_dummy_1056 h) (nb078_wpp_notmem_2680) (nb078_wpp_notmem_2681 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1047) (nb078_alpha_dummy_1048 h) (nb078_wpp_notmem_2682) (nb078_wpp_notmem_2683 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1045) (nb078_alpha_dummy_1046 h) (nb078_wpp_notmem_2684) (nb078_wpp_notmem_2685 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1964) (nb078_wpp_notmem_1965 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))

noncomputable def nb078_wpp_refl_0488 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_1223), (nb078_alpha_dummy_1226 h)), ((nb078_alpha_dummy_1222), (nb078_alpha_dummy_1225 h)), ((nb078_alpha_dummy_1221), (nb078_alpha_dummy_1224 h)), ((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)), ((nb078_alpha_dummy_1215), (nb078_alpha_dummy_1217 h)), ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)), ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)), ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)), ((nb078_alpha_dummy_1213), (nb078_alpha_dummy_1214 h)), ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0488 x y h)

theorem nb078_wpp_notmem_3076 : (nb078_alpha_dummy_1223) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0912)

theorem nb078_wpp_notmem_3077 (h : Var) : (nb078_alpha_dummy_1226 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0913 h)

theorem nb078_wpp_notmem_3078 : (nb078_alpha_dummy_1222) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0914)

theorem nb078_wpp_notmem_3079 (h : Var) : (nb078_alpha_dummy_1225 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0915 h)

theorem nb078_wpp_notmem_3080 : (nb078_alpha_dummy_1221) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0916)

theorem nb078_wpp_notmem_3081 (h : Var) : (nb078_alpha_dummy_1224 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0917 h)

theorem nb078_wpp_notmem_3082 : (nb078_alpha_dummy_1219) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0918)

theorem nb078_wpp_notmem_3083 (h : Var) : (nb078_alpha_dummy_1220 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0919 h)

theorem nb078_wpp_notmem_3084 : (nb078_alpha_dummy_1215) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0920)

theorem nb078_wpp_notmem_3085 (h : Var) : (nb078_alpha_dummy_1217 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0921 h)

theorem nb078_wpp_notmem_3086 : (nb078_alpha_dummy_1216) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0922)

theorem nb078_wpp_notmem_3087 (h : Var) : (nb078_alpha_dummy_1218 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0923 h)

theorem nb078_wpp_notmem_3088 : (nb078_alpha_dummy_1208) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0924)

theorem nb078_wpp_notmem_3089 (h : Var) : (nb078_alpha_dummy_1210 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0925 h)

theorem nb078_wpp_notmem_3090 : (nb078_alpha_dummy_1207) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0926)

theorem nb078_wpp_notmem_3091 (h : Var) : (nb078_alpha_dummy_1209 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0927 h)

theorem nb078_wpp_notmem_3092 : (nb078_alpha_dummy_1213) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0928)

theorem nb078_wpp_notmem_3093 (h : Var) : (nb078_alpha_dummy_1214 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0929 h)

theorem nb078_wpp_notmem_3094 : (nb078_alpha_dummy_1211) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0930)

theorem nb078_wpp_notmem_3095 (h : Var) : (nb078_alpha_dummy_1212 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0931 h)

theorem nb078_compact_envfresh_0489 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_1223), (nb078_alpha_dummy_1226 h)), ((nb078_alpha_dummy_1222), (nb078_alpha_dummy_1225 h)), ((nb078_alpha_dummy_1221), (nb078_alpha_dummy_1224 h)), ((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)), ((nb078_alpha_dummy_1215), (nb078_alpha_dummy_1217 h)), ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)), ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)), ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)), ((nb078_alpha_dummy_1213), (nb078_alpha_dummy_1214 h)), ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_1223) (nb078_alpha_dummy_1226 h) (nb078_wpp_notmem_3076) (nb078_wpp_notmem_3077 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1222) (nb078_alpha_dummy_1225 h) (nb078_wpp_notmem_3078) (nb078_wpp_notmem_3079 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1221) (nb078_alpha_dummy_1224 h) (nb078_wpp_notmem_3080) (nb078_wpp_notmem_3081 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1219) (nb078_alpha_dummy_1220 h) (nb078_wpp_notmem_3082) (nb078_wpp_notmem_3083 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1215) (nb078_alpha_dummy_1217 h) (nb078_wpp_notmem_3084) (nb078_wpp_notmem_3085 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1216) (nb078_alpha_dummy_1218 h) (nb078_wpp_notmem_3086) (nb078_wpp_notmem_3087 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1208) (nb078_alpha_dummy_1210 h) (nb078_wpp_notmem_3088) (nb078_wpp_notmem_3089 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1207) (nb078_alpha_dummy_1209 h) (nb078_wpp_notmem_3090) (nb078_wpp_notmem_3091 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1213) (nb078_alpha_dummy_1214 h) (nb078_wpp_notmem_3092) (nb078_wpp_notmem_3093 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1211) (nb078_alpha_dummy_1212 h) (nb078_wpp_notmem_3094) (nb078_wpp_notmem_3095 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1051) (nb078_alpha_dummy_1054 h) (nb078_wpp_notmem_2820) (nb078_wpp_notmem_2821 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1050) (nb078_alpha_dummy_1053 h) (nb078_wpp_notmem_2706) (nb078_wpp_notmem_2707 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1049) (nb078_alpha_dummy_1052 h) (nb078_wpp_notmem_2708) (nb078_wpp_notmem_2709 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1055) (nb078_alpha_dummy_1056 h) (nb078_wpp_notmem_2710) (nb078_wpp_notmem_2711 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1047) (nb078_alpha_dummy_1048 h) (nb078_wpp_notmem_2712) (nb078_wpp_notmem_2713 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1045) (nb078_alpha_dummy_1046 h) (nb078_wpp_notmem_2714) (nb078_wpp_notmem_2715 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1996) (nb078_wpp_notmem_1997 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))

noncomputable def nb078_wpp_refl_0489 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_1223), (nb078_alpha_dummy_1226 h)), ((nb078_alpha_dummy_1222), (nb078_alpha_dummy_1225 h)), ((nb078_alpha_dummy_1221), (nb078_alpha_dummy_1224 h)), ((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)), ((nb078_alpha_dummy_1215), (nb078_alpha_dummy_1217 h)), ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)), ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)), ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)), ((nb078_alpha_dummy_1213), (nb078_alpha_dummy_1214 h)), ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0489 x y h)

theorem nb078_wpp_notmem_3096 : (nb078_alpha_dummy_1219) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0918)

theorem nb078_wpp_notmem_3097 (h : Var) : (nb078_alpha_dummy_1220 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0919 h)

theorem nb078_wpp_notmem_3098 : (nb078_alpha_dummy_1215) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0920)

theorem nb078_wpp_notmem_3099 (h : Var) : (nb078_alpha_dummy_1217 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0921 h)

theorem nb078_wpp_notmem_3100 : (nb078_alpha_dummy_1216) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0922)

theorem nb078_wpp_notmem_3101 (h : Var) : (nb078_alpha_dummy_1218 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0923 h)

theorem nb078_wpp_notmem_3102 : (nb078_alpha_dummy_1208) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0924)

theorem nb078_wpp_notmem_3103 (h : Var) : (nb078_alpha_dummy_1210 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0925 h)

theorem nb078_wpp_notmem_3104 : (nb078_alpha_dummy_1207) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0926)

theorem nb078_wpp_notmem_3105 (h : Var) : (nb078_alpha_dummy_1209 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0927 h)

theorem nb078_wpp_notmem_3106 : (nb078_alpha_dummy_1213) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0928)

theorem nb078_wpp_notmem_3107 (h : Var) : (nb078_alpha_dummy_1214 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0929 h)

theorem nb078_wpp_notmem_3108 : (nb078_alpha_dummy_1211) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0930)

theorem nb078_wpp_notmem_3109 (h : Var) : (nb078_alpha_dummy_1212 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0931 h)

theorem nb078_compact_envfresh_0490 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)), ((nb078_alpha_dummy_1215), (nb078_alpha_dummy_1217 h)), ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)), ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)), ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)), ((nb078_alpha_dummy_1213), (nb078_alpha_dummy_1214 h)), ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_1219) (nb078_alpha_dummy_1220 h) (nb078_wpp_notmem_3096) (nb078_wpp_notmem_3097 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1215) (nb078_alpha_dummy_1217 h) (nb078_wpp_notmem_3098) (nb078_wpp_notmem_3099 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1216) (nb078_alpha_dummy_1218 h) (nb078_wpp_notmem_3100) (nb078_wpp_notmem_3101 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1208) (nb078_alpha_dummy_1210 h) (nb078_wpp_notmem_3102) (nb078_wpp_notmem_3103 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1207) (nb078_alpha_dummy_1209 h) (nb078_wpp_notmem_3104) (nb078_wpp_notmem_3105 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1213) (nb078_alpha_dummy_1214 h) (nb078_wpp_notmem_3106) (nb078_wpp_notmem_3107 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1211) (nb078_alpha_dummy_1212 h) (nb078_wpp_notmem_3108) (nb078_wpp_notmem_3109 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1051) (nb078_alpha_dummy_1054 h) (nb078_wpp_notmem_2836) (nb078_wpp_notmem_2837 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1050) (nb078_alpha_dummy_1053 h) (nb078_wpp_notmem_2730) (nb078_wpp_notmem_2731 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1049) (nb078_alpha_dummy_1052 h) (nb078_wpp_notmem_2732) (nb078_wpp_notmem_2733 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1055) (nb078_alpha_dummy_1056 h) (nb078_wpp_notmem_2734) (nb078_wpp_notmem_2735 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1047) (nb078_alpha_dummy_1048 h) (nb078_wpp_notmem_2736) (nb078_wpp_notmem_2737 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1045) (nb078_alpha_dummy_1046 h) (nb078_wpp_notmem_2738) (nb078_wpp_notmem_2739 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_2022) (nb078_wpp_notmem_2023 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))

noncomputable def nb078_wpp_refl_0490 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)), ((nb078_alpha_dummy_1215), (nb078_alpha_dummy_1217 h)), ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)), ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)), ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)), ((nb078_alpha_dummy_1213), (nb078_alpha_dummy_1214 h)), ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0490 x y h)

noncomputable def nb078_split_alpha_0147 (x : Var) (y : Var) (h : Var) : TAlphaWff [((nb078_alpha_dummy_1213), (nb078_alpha_dummy_1214 h)), ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1213)) (Class.cab (nb078_alpha_dummy_1207) (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1051)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1207)) (syn_cphi (Class.cv (nb078_alpha_dummy_1208))))))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_1213)) (Class.cab (nb078_alpha_dummy_1207) (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1051)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1207)) (syn_cphi (Class.cv (nb078_alpha_dummy_1208))))))))) (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1214 h)) (Class.cab (nb078_alpha_dummy_1209 h) (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1054 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h))))))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_1214 h)) (Class.cab (nb078_alpha_dummy_1209 h) (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1054 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1268) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1270 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1268) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1270 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1272) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1273 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1269) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1271 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1051))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1054 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1053 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1274) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1275 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1274) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1275 h) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1208))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1210 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1278) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1279 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1278) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1279 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1276) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1277 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1223), (nb078_alpha_dummy_1226 h)), ((nb078_alpha_dummy_1222), (nb078_alpha_dummy_1225 h)), ((nb078_alpha_dummy_1221), (nb078_alpha_dummy_1224 h)), ((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)), ((nb078_alpha_dummy_1215), (nb078_alpha_dummy_1217 h)), ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)), ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)), ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)), ((nb078_alpha_dummy_1213), (nb078_alpha_dummy_1214 h)), ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0488 x y h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1282) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1283 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1280) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1281 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1286) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1287 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1284) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1285 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1282) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1283 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1280) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1281 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1286) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1287 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1284) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1285 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1223), (nb078_alpha_dummy_1226 h)), ((nb078_alpha_dummy_1222), (nb078_alpha_dummy_1225 h)), ((nb078_alpha_dummy_1221), (nb078_alpha_dummy_1224 h)), ((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)), ((nb078_alpha_dummy_1215), (nb078_alpha_dummy_1217 h)), ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)), ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)), ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)), ((nb078_alpha_dummy_1213), (nb078_alpha_dummy_1214 h)), ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0489 x y h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1290) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1291 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1288) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1289 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1290) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1291 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1288) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1289 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1294) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1295 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1292) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1293 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1294) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1295 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1292) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1293 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1276) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1277 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)), ((nb078_alpha_dummy_1215), (nb078_alpha_dummy_1217 h)), ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)), ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)), ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)), ((nb078_alpha_dummy_1213), (nb078_alpha_dummy_1214 h)), ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0490 x y h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1276) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1277 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1276) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1277 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)), ((nb078_alpha_dummy_1215), (nb078_alpha_dummy_1217 h)), ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)), ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)), ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)), ((nb078_alpha_dummy_1213), (nb078_alpha_dummy_1214 h)), ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0490 x y h)))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1268) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1270 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1268) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1270 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1272) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1273 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1269) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1271 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1051))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1054 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1053 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1274) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1275 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1274) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1275 h) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1208))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1210 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1278) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1279 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1278) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1279 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1276) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1277 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1223), (nb078_alpha_dummy_1226 h)), ((nb078_alpha_dummy_1222), (nb078_alpha_dummy_1225 h)), ((nb078_alpha_dummy_1221), (nb078_alpha_dummy_1224 h)), ((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)), ((nb078_alpha_dummy_1215), (nb078_alpha_dummy_1217 h)), ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)), ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)), ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)), ((nb078_alpha_dummy_1213), (nb078_alpha_dummy_1214 h)), ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0488 x y h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1282) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1283 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1280) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1281 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1286) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1287 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1284) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1285 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1282) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1283 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1280) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1281 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1286) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1287 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1284) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1285 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1223), (nb078_alpha_dummy_1226 h)), ((nb078_alpha_dummy_1222), (nb078_alpha_dummy_1225 h)), ((nb078_alpha_dummy_1221), (nb078_alpha_dummy_1224 h)), ((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)), ((nb078_alpha_dummy_1215), (nb078_alpha_dummy_1217 h)), ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)), ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)), ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)), ((nb078_alpha_dummy_1213), (nb078_alpha_dummy_1214 h)), ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0489 x y h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1290) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1291 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1288) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1289 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1290) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1291 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1288) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1289 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1294) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1295 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1292) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1293 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1294) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1295 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1292) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1293 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1276) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1277 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)), ((nb078_alpha_dummy_1215), (nb078_alpha_dummy_1217 h)), ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)), ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)), ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)), ((nb078_alpha_dummy_1213), (nb078_alpha_dummy_1214 h)), ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0490 x y h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1276) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1277 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1276) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1277 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)), ((nb078_alpha_dummy_1215), (nb078_alpha_dummy_1217 h)), ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)), ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)), ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)), ((nb078_alpha_dummy_1213), (nb078_alpha_dummy_1214 h)), ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0490 x y h))))))))))))))))))))))))))))

theorem nb078_compact_fv_empty_0932 : (nb078_alpha_dummy_1241) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_3110 : (nb078_alpha_dummy_1241) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0932)

theorem nb078_compact_fv_empty_0933 (h : Var) : (nb078_alpha_dummy_1242 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_3111 (h : Var) : (nb078_alpha_dummy_1242 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0933 h)

theorem nb078_compact_fv_empty_0934 : (nb078_alpha_dummy_1239) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_3112 : (nb078_alpha_dummy_1239) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0934)

theorem nb078_compact_fv_empty_0935 (h : Var) : (nb078_alpha_dummy_1240 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_3113 (h : Var) : (nb078_alpha_dummy_1240 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0935 h)

theorem nb078_compact_fv_empty_0936 : (nb078_alpha_dummy_1237) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_3114 : (nb078_alpha_dummy_1237) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0936)

theorem nb078_compact_fv_empty_0937 (h : Var) : (nb078_alpha_dummy_1238 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_3115 (h : Var) : (nb078_alpha_dummy_1238 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0937 h)

theorem nb078_compact_envfresh_0491 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_1223), (nb078_alpha_dummy_1226 h)), ((nb078_alpha_dummy_1222), (nb078_alpha_dummy_1225 h)), ((nb078_alpha_dummy_1221), (nb078_alpha_dummy_1224 h)), ((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)), ((nb078_alpha_dummy_1215), (nb078_alpha_dummy_1217 h)), ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)), ((nb078_alpha_dummy_1241), (nb078_alpha_dummy_1242 h)), ((nb078_alpha_dummy_1239), (nb078_alpha_dummy_1240 h)), ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)), ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)), ((nb078_alpha_dummy_1237), (nb078_alpha_dummy_1238 h)), ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_1223) (nb078_alpha_dummy_1226 h) (nb078_wpp_notmem_3056) (nb078_wpp_notmem_3057 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1222) (nb078_alpha_dummy_1225 h) (nb078_wpp_notmem_3058) (nb078_wpp_notmem_3059 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1221) (nb078_alpha_dummy_1224 h) (nb078_wpp_notmem_3060) (nb078_wpp_notmem_3061 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1219) (nb078_alpha_dummy_1220 h) (nb078_wpp_notmem_3062) (nb078_wpp_notmem_3063 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1215) (nb078_alpha_dummy_1217 h) (nb078_wpp_notmem_3064) (nb078_wpp_notmem_3065 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1216) (nb078_alpha_dummy_1218 h) (nb078_wpp_notmem_3066) (nb078_wpp_notmem_3067 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1241) (nb078_alpha_dummy_1242 h) (nb078_wpp_notmem_3110) (nb078_wpp_notmem_3111 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1239) (nb078_alpha_dummy_1240 h) (nb078_wpp_notmem_3112) (nb078_wpp_notmem_3113 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1208) (nb078_alpha_dummy_1210 h) (nb078_wpp_notmem_3068) (nb078_wpp_notmem_3069 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1207) (nb078_alpha_dummy_1209 h) (nb078_wpp_notmem_3070) (nb078_wpp_notmem_3071 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1237) (nb078_alpha_dummy_1238 h) (nb078_wpp_notmem_3114) (nb078_wpp_notmem_3115 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1211) (nb078_alpha_dummy_1212 h) (nb078_wpp_notmem_3074) (nb078_wpp_notmem_3075 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1051) (nb078_alpha_dummy_1054 h) (nb078_wpp_notmem_2798) (nb078_wpp_notmem_2799 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1050) (nb078_alpha_dummy_1053 h) (nb078_wpp_notmem_2676) (nb078_wpp_notmem_2677 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1049) (nb078_alpha_dummy_1052 h) (nb078_wpp_notmem_2678) (nb078_wpp_notmem_2679 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1055) (nb078_alpha_dummy_1056 h) (nb078_wpp_notmem_2680) (nb078_wpp_notmem_2681 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1047) (nb078_alpha_dummy_1048 h) (nb078_wpp_notmem_2682) (nb078_wpp_notmem_2683 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1045) (nb078_alpha_dummy_1046 h) (nb078_wpp_notmem_2684) (nb078_wpp_notmem_2685 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1964) (nb078_wpp_notmem_1965 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))))

noncomputable def nb078_wpp_refl_0491 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_1223), (nb078_alpha_dummy_1226 h)), ((nb078_alpha_dummy_1222), (nb078_alpha_dummy_1225 h)), ((nb078_alpha_dummy_1221), (nb078_alpha_dummy_1224 h)), ((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)), ((nb078_alpha_dummy_1215), (nb078_alpha_dummy_1217 h)), ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)), ((nb078_alpha_dummy_1241), (nb078_alpha_dummy_1242 h)), ((nb078_alpha_dummy_1239), (nb078_alpha_dummy_1240 h)), ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)), ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)), ((nb078_alpha_dummy_1237), (nb078_alpha_dummy_1238 h)), ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0491 x y h)

theorem nb078_wpp_notmem_3116 : (nb078_alpha_dummy_1241) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0932)

theorem nb078_wpp_notmem_3117 (h : Var) : (nb078_alpha_dummy_1242 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0933 h)

theorem nb078_wpp_notmem_3118 : (nb078_alpha_dummy_1239) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0934)

theorem nb078_wpp_notmem_3119 (h : Var) : (nb078_alpha_dummy_1240 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0935 h)

theorem nb078_wpp_notmem_3120 : (nb078_alpha_dummy_1237) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0936)

theorem nb078_wpp_notmem_3121 (h : Var) : (nb078_alpha_dummy_1238 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0937 h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
