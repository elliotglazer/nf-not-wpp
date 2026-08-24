import NAR4C074C001Part004

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

theorem nb074_wpp_notmem_0029 (x : Var) : (nb074_alpha_dummy_023 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_023, fv_syn_c0] using (nb074_compact_fv_empty_0003 x)

theorem nb074_wpp_notmem_0030 : (nb074_alpha_dummy_019) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_019, fv_syn_c0] using (nb074_compact_fv_empty_0004)

theorem nb074_wpp_notmem_0031 (x : Var) : (nb074_alpha_dummy_022 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_022, fv_syn_c0] using (nb074_compact_fv_empty_0005 x)

theorem nb074_wpp_notmem_0032 : (nb074_alpha_dummy_017) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_017, fv_syn_c0] using (nb074_compact_fv_empty_0006)

theorem nb074_wpp_notmem_0033 (x : Var) : (nb074_alpha_dummy_018 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_018, fv_syn_c0] using (nb074_compact_fv_empty_0007 x)

theorem nb074_wpp_notmem_0034 : (nb074_alpha_dummy_013) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_013, fv_syn_c0] using (nb074_compact_fv_empty_0008)

theorem nb074_wpp_notmem_0035 (x : Var) : (nb074_alpha_dummy_015 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_015, fv_syn_c0] using (nb074_compact_fv_empty_0009 x)

theorem nb074_wpp_notmem_0036 : (nb074_alpha_dummy_014) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_014, fv_syn_c0] using (nb074_compact_fv_empty_0010)

theorem nb074_wpp_notmem_0037 (x : Var) : (nb074_alpha_dummy_016 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_016, fv_syn_c0] using (nb074_compact_fv_empty_0011 x)

theorem nb074_wpp_notmem_0038 : (nb074_alpha_dummy_006) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_006, fv_syn_c0] using (nb074_compact_fv_empty_0012)

theorem nb074_wpp_notmem_0039 (x : Var) : (nb074_alpha_dummy_008 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_008, fv_syn_c0] using (nb074_compact_fv_empty_0013 x)

theorem nb074_wpp_notmem_0040 : (nb074_alpha_dummy_005) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_005, fv_syn_c0] using (nb074_compact_fv_empty_0014)

theorem nb074_wpp_notmem_0041 (x : Var) : (nb074_alpha_dummy_007 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_007, fv_syn_c0] using (nb074_compact_fv_empty_0015 x)

theorem nb074_wpp_notmem_0042 : (nb074_alpha_dummy_011) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_011, fv_syn_c0] using (nb074_compact_fv_empty_0016)

theorem nb074_wpp_notmem_0043 (x : Var) : (nb074_alpha_dummy_012 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_012, fv_syn_c0] using (nb074_compact_fv_empty_0017 x)

theorem nb074_wpp_notmem_0044 : (nb074_alpha_dummy_009) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_009, fv_syn_c0] using (nb074_compact_fv_empty_0018)

theorem nb074_wpp_notmem_0045 (x : Var) : (nb074_alpha_dummy_010 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_010, fv_syn_c0] using (nb074_compact_fv_empty_0019 x)

theorem nb074_wpp_notmem_0046 : (nb074_alpha_dummy_001) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_001, fv_syn_c0] using (nb074_compact_fv_empty_0020)

theorem nb074_wpp_notmem_0047 (x : Var) : (nb074_alpha_dummy_002 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_002, fv_syn_c0] using (nb074_compact_fv_empty_0021 x)

theorem nb074_wpp_notmem_0048 : (nb074_alpha_dummy_000) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_000, fv_syn_c0] using (nb074_compact_fv_empty_0022)

theorem nb074_wpp_notmem_0049 (x : Var) : x ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb074_compact_fv_empty_0023 x)

theorem nb074_wpp_notmem_0050 : (nb074_alpha_dummy_003) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_003, fv_syn_c0] using (nb074_compact_fv_empty_0024)

theorem nb074_wpp_notmem_0051 (x : Var) : (nb074_alpha_dummy_004 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_004, fv_syn_c0] using (nb074_compact_fv_empty_0025 x)

theorem nb074_compact_envfresh_0001 (x : Var) : TEnvFresh [((nb074_alpha_dummy_021), (nb074_alpha_dummy_024 x)), ((nb074_alpha_dummy_020), (nb074_alpha_dummy_023 x)), ((nb074_alpha_dummy_019), (nb074_alpha_dummy_022 x)), ((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013), (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_011), (nb074_alpha_dummy_012 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb074_alpha_dummy_021) (nb074_alpha_dummy_024 x) (nb074_wpp_notmem_0026) (nb074_wpp_notmem_0027 x) (TEnvFresh.consFresh (nb074_alpha_dummy_020) (nb074_alpha_dummy_023 x) (nb074_wpp_notmem_0028) (nb074_wpp_notmem_0029 x) (TEnvFresh.consFresh (nb074_alpha_dummy_019) (nb074_alpha_dummy_022 x) (nb074_wpp_notmem_0030) (nb074_wpp_notmem_0031 x) (TEnvFresh.consFresh (nb074_alpha_dummy_017) (nb074_alpha_dummy_018 x) (nb074_wpp_notmem_0032) (nb074_wpp_notmem_0033 x) (TEnvFresh.consFresh (nb074_alpha_dummy_013) (nb074_alpha_dummy_015 x) (nb074_wpp_notmem_0034) (nb074_wpp_notmem_0035 x) (TEnvFresh.consFresh (nb074_alpha_dummy_014) (nb074_alpha_dummy_016 x) (nb074_wpp_notmem_0036) (nb074_wpp_notmem_0037 x) (TEnvFresh.consFresh (nb074_alpha_dummy_006) (nb074_alpha_dummy_008 x) (nb074_wpp_notmem_0038) (nb074_wpp_notmem_0039 x) (TEnvFresh.consFresh (nb074_alpha_dummy_005) (nb074_alpha_dummy_007 x) (nb074_wpp_notmem_0040) (nb074_wpp_notmem_0041 x) (TEnvFresh.consFresh (nb074_alpha_dummy_011) (nb074_alpha_dummy_012 x) (nb074_wpp_notmem_0042) (nb074_wpp_notmem_0043 x) (TEnvFresh.consFresh (nb074_alpha_dummy_009) (nb074_alpha_dummy_010 x) (nb074_wpp_notmem_0044) (nb074_wpp_notmem_0045 x) (TEnvFresh.consFresh (nb074_alpha_dummy_001) (nb074_alpha_dummy_002 x) (nb074_wpp_notmem_0046) (nb074_wpp_notmem_0047 x) (TEnvFresh.consFresh (nb074_alpha_dummy_000) x (nb074_wpp_notmem_0048) (nb074_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb074_alpha_dummy_003) (nb074_alpha_dummy_004 x) (nb074_wpp_notmem_0050) (nb074_wpp_notmem_0051 x) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))

noncomputable def nb074_wpp_refl_0001 (x : Var) : TReflOn [((nb074_alpha_dummy_021), (nb074_alpha_dummy_024 x)), ((nb074_alpha_dummy_020), (nb074_alpha_dummy_023 x)), ((nb074_alpha_dummy_019), (nb074_alpha_dummy_022 x)), ((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013), (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_011), (nb074_alpha_dummy_012 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb074_compact_envfresh_0001 x)

theorem nb074_wpp_notmem_0052 : (nb074_alpha_dummy_017) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_017, fv_syn_cnnc] using (nb074_compact_fv_empty_0006)

theorem nb074_wpp_notmem_0053 (x : Var) : (nb074_alpha_dummy_018 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_018, fv_syn_cnnc] using (nb074_compact_fv_empty_0007 x)

theorem nb074_wpp_notmem_0054 : (nb074_alpha_dummy_013) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_013, fv_syn_cnnc] using (nb074_compact_fv_empty_0008)

theorem nb074_wpp_notmem_0055 (x : Var) : (nb074_alpha_dummy_015 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_015, fv_syn_cnnc] using (nb074_compact_fv_empty_0009 x)

theorem nb074_wpp_notmem_0056 : (nb074_alpha_dummy_014) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_014, fv_syn_cnnc] using (nb074_compact_fv_empty_0010)

theorem nb074_wpp_notmem_0057 (x : Var) : (nb074_alpha_dummy_016 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_016, fv_syn_cnnc] using (nb074_compact_fv_empty_0011 x)

theorem nb074_wpp_notmem_0058 : (nb074_alpha_dummy_006) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_006, fv_syn_cnnc] using (nb074_compact_fv_empty_0012)

theorem nb074_wpp_notmem_0059 (x : Var) : (nb074_alpha_dummy_008 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_008, fv_syn_cnnc] using (nb074_compact_fv_empty_0013 x)

theorem nb074_wpp_notmem_0060 : (nb074_alpha_dummy_005) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_005, fv_syn_cnnc] using (nb074_compact_fv_empty_0014)

theorem nb074_wpp_notmem_0061 (x : Var) : (nb074_alpha_dummy_007 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_007, fv_syn_cnnc] using (nb074_compact_fv_empty_0015 x)

theorem nb074_wpp_notmem_0062 : (nb074_alpha_dummy_011) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_011, fv_syn_cnnc] using (nb074_compact_fv_empty_0016)

theorem nb074_wpp_notmem_0063 (x : Var) : (nb074_alpha_dummy_012 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_012, fv_syn_cnnc] using (nb074_compact_fv_empty_0017 x)

theorem nb074_wpp_notmem_0064 : (nb074_alpha_dummy_009) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_009, fv_syn_cnnc] using (nb074_compact_fv_empty_0018)

theorem nb074_wpp_notmem_0065 (x : Var) : (nb074_alpha_dummy_010 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_010, fv_syn_cnnc] using (nb074_compact_fv_empty_0019 x)

theorem nb074_wpp_notmem_0066 : (nb074_alpha_dummy_001) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_001, fv_syn_cnnc] using (nb074_compact_fv_empty_0020)

theorem nb074_wpp_notmem_0067 (x : Var) : (nb074_alpha_dummy_002 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_002, fv_syn_cnnc] using (nb074_compact_fv_empty_0021 x)

theorem nb074_wpp_notmem_0068 : (nb074_alpha_dummy_000) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_000, fv_syn_cnnc] using (nb074_compact_fv_empty_0022)

theorem nb074_wpp_notmem_0069 (x : Var) : x ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb074_compact_fv_empty_0023 x)

theorem nb074_wpp_notmem_0070 : (nb074_alpha_dummy_003) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_003, fv_syn_cnnc] using (nb074_compact_fv_empty_0024)

theorem nb074_wpp_notmem_0071 (x : Var) : (nb074_alpha_dummy_004 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_004, fv_syn_cnnc] using (nb074_compact_fv_empty_0025 x)

theorem nb074_compact_envfresh_0002 (x : Var) : TEnvFresh [((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013), (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_011), (nb074_alpha_dummy_012 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb074_alpha_dummy_017) (nb074_alpha_dummy_018 x) (nb074_wpp_notmem_0052) (nb074_wpp_notmem_0053 x) (TEnvFresh.consFresh (nb074_alpha_dummy_013) (nb074_alpha_dummy_015 x) (nb074_wpp_notmem_0054) (nb074_wpp_notmem_0055 x) (TEnvFresh.consFresh (nb074_alpha_dummy_014) (nb074_alpha_dummy_016 x) (nb074_wpp_notmem_0056) (nb074_wpp_notmem_0057 x) (TEnvFresh.consFresh (nb074_alpha_dummy_006) (nb074_alpha_dummy_008 x) (nb074_wpp_notmem_0058) (nb074_wpp_notmem_0059 x) (TEnvFresh.consFresh (nb074_alpha_dummy_005) (nb074_alpha_dummy_007 x) (nb074_wpp_notmem_0060) (nb074_wpp_notmem_0061 x) (TEnvFresh.consFresh (nb074_alpha_dummy_011) (nb074_alpha_dummy_012 x) (nb074_wpp_notmem_0062) (nb074_wpp_notmem_0063 x) (TEnvFresh.consFresh (nb074_alpha_dummy_009) (nb074_alpha_dummy_010 x) (nb074_wpp_notmem_0064) (nb074_wpp_notmem_0065 x) (TEnvFresh.consFresh (nb074_alpha_dummy_001) (nb074_alpha_dummy_002 x) (nb074_wpp_notmem_0066) (nb074_wpp_notmem_0067 x) (TEnvFresh.consFresh (nb074_alpha_dummy_000) x (nb074_wpp_notmem_0068) (nb074_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb074_alpha_dummy_003) (nb074_alpha_dummy_004 x) (nb074_wpp_notmem_0070) (nb074_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))

noncomputable def nb074_wpp_refl_0002 (x : Var) : TReflOn [((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013), (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_011), (nb074_alpha_dummy_012 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb074_compact_envfresh_0002 x)

theorem nb074_compact_fv_empty_0026 : (nb074_alpha_dummy_039) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0072 : (nb074_alpha_dummy_039) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_039, fv_syn_c1c] using (nb074_compact_fv_empty_0026)

theorem nb074_compact_fv_empty_0027 (x : Var) : (nb074_alpha_dummy_040 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0073 (x : Var) : (nb074_alpha_dummy_040 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_040, fv_syn_c1c] using (nb074_compact_fv_empty_0027 x)

theorem nb074_compact_fv_empty_0028 : (nb074_alpha_dummy_037) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0074 : (nb074_alpha_dummy_037) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_037, fv_syn_c1c] using (nb074_compact_fv_empty_0028)

theorem nb074_compact_fv_empty_0029 (x : Var) : (nb074_alpha_dummy_038 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0075 (x : Var) : (nb074_alpha_dummy_038 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_038, fv_syn_c1c] using (nb074_compact_fv_empty_0029 x)

theorem nb074_compact_fv_empty_0030 : (nb074_alpha_dummy_035) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0076 : (nb074_alpha_dummy_035) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_035, fv_syn_c1c] using (nb074_compact_fv_empty_0030)

theorem nb074_compact_fv_empty_0031 (x : Var) : (nb074_alpha_dummy_036 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0077 (x : Var) : (nb074_alpha_dummy_036 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_036, fv_syn_c1c] using (nb074_compact_fv_empty_0031 x)

theorem nb074_compact_envfresh_0003 (x : Var) : TEnvFresh [((nb074_alpha_dummy_021), (nb074_alpha_dummy_024 x)), ((nb074_alpha_dummy_020), (nb074_alpha_dummy_023 x)), ((nb074_alpha_dummy_019), (nb074_alpha_dummy_022 x)), ((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013), (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)), ((nb074_alpha_dummy_039), (nb074_alpha_dummy_040 x)), ((nb074_alpha_dummy_037), (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035), (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb074_alpha_dummy_021) (nb074_alpha_dummy_024 x) (nb074_wpp_notmem_0000) (nb074_wpp_notmem_0001 x) (TEnvFresh.consFresh (nb074_alpha_dummy_020) (nb074_alpha_dummy_023 x) (nb074_wpp_notmem_0002) (nb074_wpp_notmem_0003 x) (TEnvFresh.consFresh (nb074_alpha_dummy_019) (nb074_alpha_dummy_022 x) (nb074_wpp_notmem_0004) (nb074_wpp_notmem_0005 x) (TEnvFresh.consFresh (nb074_alpha_dummy_017) (nb074_alpha_dummy_018 x) (nb074_wpp_notmem_0006) (nb074_wpp_notmem_0007 x) (TEnvFresh.consFresh (nb074_alpha_dummy_013) (nb074_alpha_dummy_015 x) (nb074_wpp_notmem_0008) (nb074_wpp_notmem_0009 x) (TEnvFresh.consFresh (nb074_alpha_dummy_014) (nb074_alpha_dummy_016 x) (nb074_wpp_notmem_0010) (nb074_wpp_notmem_0011 x) (TEnvFresh.consFresh (nb074_alpha_dummy_039) (nb074_alpha_dummy_040 x) (nb074_wpp_notmem_0072) (nb074_wpp_notmem_0073 x) (TEnvFresh.consFresh (nb074_alpha_dummy_037) (nb074_alpha_dummy_038 x) (nb074_wpp_notmem_0074) (nb074_wpp_notmem_0075 x) (TEnvFresh.consFresh (nb074_alpha_dummy_006) (nb074_alpha_dummy_008 x) (nb074_wpp_notmem_0012) (nb074_wpp_notmem_0013 x) (TEnvFresh.consFresh (nb074_alpha_dummy_005) (nb074_alpha_dummy_007 x) (nb074_wpp_notmem_0014) (nb074_wpp_notmem_0015 x) (TEnvFresh.consFresh (nb074_alpha_dummy_035) (nb074_alpha_dummy_036 x) (nb074_wpp_notmem_0076) (nb074_wpp_notmem_0077 x) (TEnvFresh.consFresh (nb074_alpha_dummy_009) (nb074_alpha_dummy_010 x) (nb074_wpp_notmem_0018) (nb074_wpp_notmem_0019 x) (TEnvFresh.consFresh (nb074_alpha_dummy_001) (nb074_alpha_dummy_002 x) (nb074_wpp_notmem_0020) (nb074_wpp_notmem_0021 x) (TEnvFresh.consFresh (nb074_alpha_dummy_000) x (nb074_wpp_notmem_0022) (nb074_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb074_alpha_dummy_003) (nb074_alpha_dummy_004 x) (nb074_wpp_notmem_0024) (nb074_wpp_notmem_0025 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb074_wpp_refl_0003 (x : Var) : TReflOn [((nb074_alpha_dummy_021), (nb074_alpha_dummy_024 x)), ((nb074_alpha_dummy_020), (nb074_alpha_dummy_023 x)), ((nb074_alpha_dummy_019), (nb074_alpha_dummy_022 x)), ((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013), (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)), ((nb074_alpha_dummy_039), (nb074_alpha_dummy_040 x)), ((nb074_alpha_dummy_037), (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035), (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb074_compact_envfresh_0003 x)

theorem nb074_wpp_notmem_0078 : (nb074_alpha_dummy_039) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_039, fv_syn_c0] using (nb074_compact_fv_empty_0026)

theorem nb074_wpp_notmem_0079 (x : Var) : (nb074_alpha_dummy_040 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_040, fv_syn_c0] using (nb074_compact_fv_empty_0027 x)

theorem nb074_wpp_notmem_0080 : (nb074_alpha_dummy_037) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_037, fv_syn_c0] using (nb074_compact_fv_empty_0028)

theorem nb074_wpp_notmem_0081 (x : Var) : (nb074_alpha_dummy_038 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_038, fv_syn_c0] using (nb074_compact_fv_empty_0029 x)

theorem nb074_wpp_notmem_0082 : (nb074_alpha_dummy_035) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_035, fv_syn_c0] using (nb074_compact_fv_empty_0030)

theorem nb074_wpp_notmem_0083 (x : Var) : (nb074_alpha_dummy_036 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_036, fv_syn_c0] using (nb074_compact_fv_empty_0031 x)

theorem nb074_compact_envfresh_0004 (x : Var) : TEnvFresh [((nb074_alpha_dummy_021), (nb074_alpha_dummy_024 x)), ((nb074_alpha_dummy_020), (nb074_alpha_dummy_023 x)), ((nb074_alpha_dummy_019), (nb074_alpha_dummy_022 x)), ((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013), (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)), ((nb074_alpha_dummy_039), (nb074_alpha_dummy_040 x)), ((nb074_alpha_dummy_037), (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035), (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb074_alpha_dummy_021) (nb074_alpha_dummy_024 x) (nb074_wpp_notmem_0026) (nb074_wpp_notmem_0027 x) (TEnvFresh.consFresh (nb074_alpha_dummy_020) (nb074_alpha_dummy_023 x) (nb074_wpp_notmem_0028) (nb074_wpp_notmem_0029 x) (TEnvFresh.consFresh (nb074_alpha_dummy_019) (nb074_alpha_dummy_022 x) (nb074_wpp_notmem_0030) (nb074_wpp_notmem_0031 x) (TEnvFresh.consFresh (nb074_alpha_dummy_017) (nb074_alpha_dummy_018 x) (nb074_wpp_notmem_0032) (nb074_wpp_notmem_0033 x) (TEnvFresh.consFresh (nb074_alpha_dummy_013) (nb074_alpha_dummy_015 x) (nb074_wpp_notmem_0034) (nb074_wpp_notmem_0035 x) (TEnvFresh.consFresh (nb074_alpha_dummy_014) (nb074_alpha_dummy_016 x) (nb074_wpp_notmem_0036) (nb074_wpp_notmem_0037 x) (TEnvFresh.consFresh (nb074_alpha_dummy_039) (nb074_alpha_dummy_040 x) (nb074_wpp_notmem_0078) (nb074_wpp_notmem_0079 x) (TEnvFresh.consFresh (nb074_alpha_dummy_037) (nb074_alpha_dummy_038 x) (nb074_wpp_notmem_0080) (nb074_wpp_notmem_0081 x) (TEnvFresh.consFresh (nb074_alpha_dummy_006) (nb074_alpha_dummy_008 x) (nb074_wpp_notmem_0038) (nb074_wpp_notmem_0039 x) (TEnvFresh.consFresh (nb074_alpha_dummy_005) (nb074_alpha_dummy_007 x) (nb074_wpp_notmem_0040) (nb074_wpp_notmem_0041 x) (TEnvFresh.consFresh (nb074_alpha_dummy_035) (nb074_alpha_dummy_036 x) (nb074_wpp_notmem_0082) (nb074_wpp_notmem_0083 x) (TEnvFresh.consFresh (nb074_alpha_dummy_009) (nb074_alpha_dummy_010 x) (nb074_wpp_notmem_0044) (nb074_wpp_notmem_0045 x) (TEnvFresh.consFresh (nb074_alpha_dummy_001) (nb074_alpha_dummy_002 x) (nb074_wpp_notmem_0046) (nb074_wpp_notmem_0047 x) (TEnvFresh.consFresh (nb074_alpha_dummy_000) x (nb074_wpp_notmem_0048) (nb074_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb074_alpha_dummy_003) (nb074_alpha_dummy_004 x) (nb074_wpp_notmem_0050) (nb074_wpp_notmem_0051 x) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))

noncomputable def nb074_wpp_refl_0004 (x : Var) : TReflOn [((nb074_alpha_dummy_021), (nb074_alpha_dummy_024 x)), ((nb074_alpha_dummy_020), (nb074_alpha_dummy_023 x)), ((nb074_alpha_dummy_019), (nb074_alpha_dummy_022 x)), ((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013), (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)), ((nb074_alpha_dummy_039), (nb074_alpha_dummy_040 x)), ((nb074_alpha_dummy_037), (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035), (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb074_compact_envfresh_0004 x)

theorem nb074_wpp_notmem_0084 : (nb074_alpha_dummy_039) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_039, fv_syn_cnnc] using (nb074_compact_fv_empty_0026)

theorem nb074_wpp_notmem_0085 (x : Var) : (nb074_alpha_dummy_040 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_040, fv_syn_cnnc] using (nb074_compact_fv_empty_0027 x)

theorem nb074_wpp_notmem_0086 : (nb074_alpha_dummy_037) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_037, fv_syn_cnnc] using (nb074_compact_fv_empty_0028)

theorem nb074_wpp_notmem_0087 (x : Var) : (nb074_alpha_dummy_038 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_038, fv_syn_cnnc] using (nb074_compact_fv_empty_0029 x)

theorem nb074_wpp_notmem_0088 : (nb074_alpha_dummy_035) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_035, fv_syn_cnnc] using (nb074_compact_fv_empty_0030)

theorem nb074_wpp_notmem_0089 (x : Var) : (nb074_alpha_dummy_036 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_036, fv_syn_cnnc] using (nb074_compact_fv_empty_0031 x)

theorem nb074_compact_envfresh_0005 (x : Var) : TEnvFresh [((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013), (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)), ((nb074_alpha_dummy_039), (nb074_alpha_dummy_040 x)), ((nb074_alpha_dummy_037), (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035), (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb074_alpha_dummy_017) (nb074_alpha_dummy_018 x) (nb074_wpp_notmem_0052) (nb074_wpp_notmem_0053 x) (TEnvFresh.consFresh (nb074_alpha_dummy_013) (nb074_alpha_dummy_015 x) (nb074_wpp_notmem_0054) (nb074_wpp_notmem_0055 x) (TEnvFresh.consFresh (nb074_alpha_dummy_014) (nb074_alpha_dummy_016 x) (nb074_wpp_notmem_0056) (nb074_wpp_notmem_0057 x) (TEnvFresh.consFresh (nb074_alpha_dummy_039) (nb074_alpha_dummy_040 x) (nb074_wpp_notmem_0084) (nb074_wpp_notmem_0085 x) (TEnvFresh.consFresh (nb074_alpha_dummy_037) (nb074_alpha_dummy_038 x) (nb074_wpp_notmem_0086) (nb074_wpp_notmem_0087 x) (TEnvFresh.consFresh (nb074_alpha_dummy_006) (nb074_alpha_dummy_008 x) (nb074_wpp_notmem_0058) (nb074_wpp_notmem_0059 x) (TEnvFresh.consFresh (nb074_alpha_dummy_005) (nb074_alpha_dummy_007 x) (nb074_wpp_notmem_0060) (nb074_wpp_notmem_0061 x) (TEnvFresh.consFresh (nb074_alpha_dummy_035) (nb074_alpha_dummy_036 x) (nb074_wpp_notmem_0088) (nb074_wpp_notmem_0089 x) (TEnvFresh.consFresh (nb074_alpha_dummy_009) (nb074_alpha_dummy_010 x) (nb074_wpp_notmem_0064) (nb074_wpp_notmem_0065 x) (TEnvFresh.consFresh (nb074_alpha_dummy_001) (nb074_alpha_dummy_002 x) (nb074_wpp_notmem_0066) (nb074_wpp_notmem_0067 x) (TEnvFresh.consFresh (nb074_alpha_dummy_000) x (nb074_wpp_notmem_0068) (nb074_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb074_alpha_dummy_003) (nb074_alpha_dummy_004 x) (nb074_wpp_notmem_0070) (nb074_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))

noncomputable def nb074_wpp_refl_0005 (x : Var) : TReflOn [((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013), (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)), ((nb074_alpha_dummy_039), (nb074_alpha_dummy_040 x)), ((nb074_alpha_dummy_037), (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035), (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb074_compact_envfresh_0005 x)

theorem nb074_wpp_notmem_0090 : (nb074_alpha_dummy_037) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_037, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0028)

theorem nb074_wpp_notmem_0091 (x : Var) : (nb074_alpha_dummy_038 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_038, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0029 x)

theorem nb074_wpp_notmem_0092 : (nb074_alpha_dummy_006) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_006, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0012)

theorem nb074_wpp_notmem_0093 (x : Var) : (nb074_alpha_dummy_008 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_008, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0013 x)

theorem nb074_wpp_notmem_0094 : (nb074_alpha_dummy_005) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_005, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0014)

theorem nb074_wpp_notmem_0095 (x : Var) : (nb074_alpha_dummy_007 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_007, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0015 x)

theorem nb074_wpp_notmem_0096 : (nb074_alpha_dummy_035) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_035, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0030)

theorem nb074_wpp_notmem_0097 (x : Var) : (nb074_alpha_dummy_036 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_036, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0031 x)

theorem nb074_wpp_notmem_0098 : (nb074_alpha_dummy_009) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_009, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0018)

theorem nb074_wpp_notmem_0099 (x : Var) : (nb074_alpha_dummy_010 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_010, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0019 x)

theorem nb074_wpp_notmem_0100 : (nb074_alpha_dummy_001) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_001, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0020)

theorem nb074_wpp_notmem_0101 (x : Var) : (nb074_alpha_dummy_002 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_002, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0021 x)

theorem nb074_wpp_notmem_0102 : (nb074_alpha_dummy_000) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_000, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0022)

theorem nb074_wpp_notmem_0103 (x : Var) : x ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0023 x)

theorem nb074_wpp_notmem_0104 : (nb074_alpha_dummy_003) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_003, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0024)

theorem nb074_wpp_notmem_0105 (x : Var) : (nb074_alpha_dummy_004 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_004, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0025 x)

theorem nb074_compact_envfresh_0006 (x : Var) : TEnvFresh [((nb074_alpha_dummy_037), (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035), (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb074_alpha_dummy_037) (nb074_alpha_dummy_038 x) (nb074_wpp_notmem_0090) (nb074_wpp_notmem_0091 x) (TEnvFresh.consFresh (nb074_alpha_dummy_006) (nb074_alpha_dummy_008 x) (nb074_wpp_notmem_0092) (nb074_wpp_notmem_0093 x) (TEnvFresh.consFresh (nb074_alpha_dummy_005) (nb074_alpha_dummy_007 x) (nb074_wpp_notmem_0094) (nb074_wpp_notmem_0095 x) (TEnvFresh.consFresh (nb074_alpha_dummy_035) (nb074_alpha_dummy_036 x) (nb074_wpp_notmem_0096) (nb074_wpp_notmem_0097 x) (TEnvFresh.consFresh (nb074_alpha_dummy_009) (nb074_alpha_dummy_010 x) (nb074_wpp_notmem_0098) (nb074_wpp_notmem_0099 x) (TEnvFresh.consFresh (nb074_alpha_dummy_001) (nb074_alpha_dummy_002 x) (nb074_wpp_notmem_0100) (nb074_wpp_notmem_0101 x) (TEnvFresh.consFresh (nb074_alpha_dummy_000) x (nb074_wpp_notmem_0102) (nb074_wpp_notmem_0103 x) (TEnvFresh.consFresh (nb074_alpha_dummy_003) (nb074_alpha_dummy_004 x) (nb074_wpp_notmem_0104) (nb074_wpp_notmem_0105 x) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))

noncomputable def nb074_wpp_refl_0006 (x : Var) : TReflOn [((nb074_alpha_dummy_037), (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035), (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb074_compact_envfresh_0006 x)

noncomputable def nb074_split_alpha_0000 (x : Var) : TAlphaWff [((nb074_alpha_dummy_035), (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (Wff.neg (Wff.classMem (Class.cv (nb074_alpha_dummy_035)) (Class.cab (nb074_alpha_dummy_005) (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001)) (Wff.classEq (Class.cv (nb074_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006))) (syn_csn (syn_c0c)))))))) (Wff.neg (Wff.classMem (Class.cv (nb074_alpha_dummy_036 x)) (Class.cab (nb074_alpha_dummy_007 x) (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x))) (syn_csn (syn_c0c)))))))) :=
  (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0034) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0036 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0034) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0036 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0038) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0039 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0035) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0037 x) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_000))).fv ∪ ((Class.cv (nb074_alpha_dummy_001))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb074_alpha_dummy_002 x))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0013 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0012) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0013 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0042) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0043 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0040) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0041 x) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_006))).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_008 x))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0016) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0017 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0017 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb074_alpha_dummy_021), (nb074_alpha_dummy_024 x)), ((nb074_alpha_dummy_020), (nb074_alpha_dummy_023 x)), ((nb074_alpha_dummy_019), (nb074_alpha_dummy_022 x)), ((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013), (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)), ((nb074_alpha_dummy_039), (nb074_alpha_dummy_040 x)), ((nb074_alpha_dummy_037), (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035), (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_c1c) (nb074_wpp_refl_0003 x))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0021 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0019 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0025 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0023 x) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0021 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0019 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0025 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0023 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb074_alpha_dummy_021), (nb074_alpha_dummy_024 x)), ((nb074_alpha_dummy_020), (nb074_alpha_dummy_023 x)), ((nb074_alpha_dummy_019), (nb074_alpha_dummy_022 x)), ((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013), (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)), ((nb074_alpha_dummy_039), (nb074_alpha_dummy_040 x)), ((nb074_alpha_dummy_037), (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035), (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_c0) (nb074_wpp_refl_0004 x))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0029 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0027 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0029 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0027 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0033 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0031 x) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0033 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0031 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013), (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)), ((nb074_alpha_dummy_039), (nb074_alpha_dummy_040 x)), ((nb074_alpha_dummy_037), (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035), (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_cnnc) (nb074_wpp_refl_0005 x))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013), (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)), ((nb074_alpha_dummy_039), (nb074_alpha_dummy_040 x)), ((nb074_alpha_dummy_037), (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035), (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_cnnc) (nb074_wpp_refl_0005 x)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0013 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0012) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0013 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0042) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0043 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0040) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0041 x) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_006))).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_008 x))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0016) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0017 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0017 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb074_alpha_dummy_021), (nb074_alpha_dummy_024 x)), ((nb074_alpha_dummy_020), (nb074_alpha_dummy_023 x)), ((nb074_alpha_dummy_019), (nb074_alpha_dummy_022 x)), ((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013), (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)), ((nb074_alpha_dummy_039), (nb074_alpha_dummy_040 x)), ((nb074_alpha_dummy_037), (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035), (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_c1c) (nb074_wpp_refl_0003 x))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0021 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0019 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0025 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0023 x) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0021 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0019 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0025 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0023 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb074_alpha_dummy_021), (nb074_alpha_dummy_024 x)), ((nb074_alpha_dummy_020), (nb074_alpha_dummy_023 x)), ((nb074_alpha_dummy_019), (nb074_alpha_dummy_022 x)), ((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013), (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)), ((nb074_alpha_dummy_039), (nb074_alpha_dummy_040 x)), ((nb074_alpha_dummy_037), (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035), (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_c0) (nb074_wpp_refl_0004 x))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0029 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0027 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0029 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0027 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0033 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0031 x) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0033 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0031 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013), (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)), ((nb074_alpha_dummy_039), (nb074_alpha_dummy_040 x)), ((nb074_alpha_dummy_037), (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035), (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_cnnc) (nb074_wpp_refl_0005 x))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013), (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)), ((nb074_alpha_dummy_039), (nb074_alpha_dummy_040 x)), ((nb074_alpha_dummy_037), (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035), (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_cnnc) (nb074_wpp_refl_0005 x)))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb074_alpha_dummy_037), (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035), (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_ccompl (syn_csn (syn_c0c))) (nb074_wpp_refl_0006 x))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
