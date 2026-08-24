import NAR4C073C001Part003

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

theorem nb073_wpp_notmem_0022 : (nb073_alpha_dummy_006) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_006, fv_syn_c1c] using (nb073_compact_fv_empty_0022)

theorem nb073_compact_fv_empty_0023 (x : Var) (y : Var) : (nb073_alpha_dummy_008 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0023 (x : Var) (y : Var) : (nb073_alpha_dummy_008 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_008, fv_syn_c1c] using (nb073_compact_fv_empty_0023 x y)

theorem nb073_compact_fv_empty_0024 : (nb073_alpha_dummy_012) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0024 : (nb073_alpha_dummy_012) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_012, fv_syn_c1c] using (nb073_compact_fv_empty_0024)

theorem nb073_compact_fv_empty_0025 (x : Var) (y : Var) : (nb073_alpha_dummy_013 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0025 (x : Var) (y : Var) : (nb073_alpha_dummy_013 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_013, fv_syn_c1c] using (nb073_compact_fv_empty_0025 x y)

theorem nb073_compact_fv_empty_0026 : (nb073_alpha_dummy_010) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0026 : (nb073_alpha_dummy_010) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_010, fv_syn_c1c] using (nb073_compact_fv_empty_0026)

theorem nb073_compact_fv_empty_0027 (x : Var) (y : Var) : (nb073_alpha_dummy_011 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0027 (x : Var) (y : Var) : (nb073_alpha_dummy_011 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_011, fv_syn_c1c] using (nb073_compact_fv_empty_0027 x y)

theorem nb073_compact_fv_empty_0028 : (nb073_alpha_dummy_002) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0028 : (nb073_alpha_dummy_002) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_002, fv_syn_c1c] using (nb073_compact_fv_empty_0028)

theorem nb073_compact_fv_empty_0029 (x : Var) (y : Var) : (nb073_alpha_dummy_003 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0029 (x : Var) (y : Var) : (nb073_alpha_dummy_003 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_003, fv_syn_c1c] using (nb073_compact_fv_empty_0029 x y)

theorem nb073_compact_fv_empty_0030 : (nb073_alpha_dummy_001) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0030 : (nb073_alpha_dummy_001) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_001, fv_syn_c1c] using (nb073_compact_fv_empty_0030)

theorem nb073_compact_fv_empty_0031 (y : Var) : y ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0031 (y : Var) : y ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb073_compact_fv_empty_0031 y)

theorem nb073_compact_fv_empty_0032 : (nb073_alpha_dummy_000) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0032 : (nb073_alpha_dummy_000) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_000, fv_syn_c1c] using (nb073_compact_fv_empty_0032)

theorem nb073_compact_fv_empty_0033 (x : Var) : x ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0033 (x : Var) : x ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb073_compact_fv_empty_0033 x)

theorem nb073_compact_fv_empty_0034 : (nb073_alpha_dummy_004) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0034 : (nb073_alpha_dummy_004) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_004, fv_syn_c1c] using (nb073_compact_fv_empty_0034)

theorem nb073_compact_fv_empty_0035 (x : Var) (y : Var) : (nb073_alpha_dummy_005 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0035 (x : Var) (y : Var) : (nb073_alpha_dummy_005 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_005, fv_syn_c1c] using (nb073_compact_fv_empty_0035 x y)

theorem nb073_compact_envfresh_0000 (x : Var) (y : Var) : TEnvFresh [((nb073_alpha_dummy_030), (nb073_alpha_dummy_033 x y)), ((nb073_alpha_dummy_029), (nb073_alpha_dummy_032 x y)), ((nb073_alpha_dummy_028), (nb073_alpha_dummy_031 x y)), ((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)), ((nb073_alpha_dummy_022), (nb073_alpha_dummy_024 x y)), ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)), ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_020), (nb073_alpha_dummy_021 x y)), ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)), ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb073_alpha_dummy_030) (nb073_alpha_dummy_033 x y) (nb073_wpp_notmem_0000) (nb073_wpp_notmem_0001 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_029) (nb073_alpha_dummy_032 x y) (nb073_wpp_notmem_0002) (nb073_wpp_notmem_0003 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_028) (nb073_alpha_dummy_031 x y) (nb073_wpp_notmem_0004) (nb073_wpp_notmem_0005 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_026) (nb073_alpha_dummy_027 x y) (nb073_wpp_notmem_0006) (nb073_wpp_notmem_0007 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_022) (nb073_alpha_dummy_024 x y) (nb073_wpp_notmem_0008) (nb073_wpp_notmem_0009 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_023) (nb073_alpha_dummy_025 x y) (nb073_wpp_notmem_0010) (nb073_wpp_notmem_0011 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_015) (nb073_alpha_dummy_017 x y) (nb073_wpp_notmem_0012) (nb073_wpp_notmem_0013 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_014) (nb073_alpha_dummy_016 x y) (nb073_wpp_notmem_0014) (nb073_wpp_notmem_0015 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_020) (nb073_alpha_dummy_021 x y) (nb073_wpp_notmem_0016) (nb073_wpp_notmem_0017 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_018) (nb073_alpha_dummy_019 x y) (nb073_wpp_notmem_0018) (nb073_wpp_notmem_0019 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_007) (nb073_alpha_dummy_009 x y) (nb073_wpp_notmem_0020) (nb073_wpp_notmem_0021 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_006) (nb073_alpha_dummy_008 x y) (nb073_wpp_notmem_0022) (nb073_wpp_notmem_0023 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_012) (nb073_alpha_dummy_013 x y) (nb073_wpp_notmem_0024) (nb073_wpp_notmem_0025 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_010) (nb073_alpha_dummy_011 x y) (nb073_wpp_notmem_0026) (nb073_wpp_notmem_0027 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_002) (nb073_alpha_dummy_003 x y) (nb073_wpp_notmem_0028) (nb073_wpp_notmem_0029 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_001) y (nb073_wpp_notmem_0030) (nb073_wpp_notmem_0031 y) (TEnvFresh.consFresh (nb073_alpha_dummy_000) x (nb073_wpp_notmem_0032) (nb073_wpp_notmem_0033 x) (TEnvFresh.consFresh (nb073_alpha_dummy_004) (nb073_alpha_dummy_005 x y) (nb073_wpp_notmem_0034) (nb073_wpp_notmem_0035 x y) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))

noncomputable def nb073_wpp_refl_0000 (x : Var) (y : Var) : TReflOn [((nb073_alpha_dummy_030), (nb073_alpha_dummy_033 x y)), ((nb073_alpha_dummy_029), (nb073_alpha_dummy_032 x y)), ((nb073_alpha_dummy_028), (nb073_alpha_dummy_031 x y)), ((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)), ((nb073_alpha_dummy_022), (nb073_alpha_dummy_024 x y)), ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)), ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_020), (nb073_alpha_dummy_021 x y)), ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)), ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb073_compact_envfresh_0000 x y)

theorem nb073_wpp_notmem_0036 : (nb073_alpha_dummy_030) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_030, fv_syn_c0] using (nb073_compact_fv_empty_0000)

theorem nb073_wpp_notmem_0037 (x : Var) (y : Var) : (nb073_alpha_dummy_033 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_033, fv_syn_c0] using (nb073_compact_fv_empty_0001 x y)

theorem nb073_wpp_notmem_0038 : (nb073_alpha_dummy_029) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_029, fv_syn_c0] using (nb073_compact_fv_empty_0002)

theorem nb073_wpp_notmem_0039 (x : Var) (y : Var) : (nb073_alpha_dummy_032 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_032, fv_syn_c0] using (nb073_compact_fv_empty_0003 x y)

theorem nb073_wpp_notmem_0040 : (nb073_alpha_dummy_028) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_028, fv_syn_c0] using (nb073_compact_fv_empty_0004)

theorem nb073_wpp_notmem_0041 (x : Var) (y : Var) : (nb073_alpha_dummy_031 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_031, fv_syn_c0] using (nb073_compact_fv_empty_0005 x y)

theorem nb073_wpp_notmem_0042 : (nb073_alpha_dummy_026) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_026, fv_syn_c0] using (nb073_compact_fv_empty_0006)

theorem nb073_wpp_notmem_0043 (x : Var) (y : Var) : (nb073_alpha_dummy_027 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_027, fv_syn_c0] using (nb073_compact_fv_empty_0007 x y)

theorem nb073_wpp_notmem_0044 : (nb073_alpha_dummy_022) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_022, fv_syn_c0] using (nb073_compact_fv_empty_0008)

theorem nb073_wpp_notmem_0045 (x : Var) (y : Var) : (nb073_alpha_dummy_024 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_024, fv_syn_c0] using (nb073_compact_fv_empty_0009 x y)

theorem nb073_wpp_notmem_0046 : (nb073_alpha_dummy_023) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_023, fv_syn_c0] using (nb073_compact_fv_empty_0010)

theorem nb073_wpp_notmem_0047 (x : Var) (y : Var) : (nb073_alpha_dummy_025 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_025, fv_syn_c0] using (nb073_compact_fv_empty_0011 x y)

theorem nb073_wpp_notmem_0048 : (nb073_alpha_dummy_015) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_015, fv_syn_c0] using (nb073_compact_fv_empty_0012)

theorem nb073_wpp_notmem_0049 (x : Var) (y : Var) : (nb073_alpha_dummy_017 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_017, fv_syn_c0] using (nb073_compact_fv_empty_0013 x y)

theorem nb073_wpp_notmem_0050 : (nb073_alpha_dummy_014) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_014, fv_syn_c0] using (nb073_compact_fv_empty_0014)

theorem nb073_wpp_notmem_0051 (x : Var) (y : Var) : (nb073_alpha_dummy_016 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_016, fv_syn_c0] using (nb073_compact_fv_empty_0015 x y)

theorem nb073_wpp_notmem_0052 : (nb073_alpha_dummy_020) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_020, fv_syn_c0] using (nb073_compact_fv_empty_0016)

theorem nb073_wpp_notmem_0053 (x : Var) (y : Var) : (nb073_alpha_dummy_021 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_021, fv_syn_c0] using (nb073_compact_fv_empty_0017 x y)

theorem nb073_wpp_notmem_0054 : (nb073_alpha_dummy_018) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_018, fv_syn_c0] using (nb073_compact_fv_empty_0018)

theorem nb073_wpp_notmem_0055 (x : Var) (y : Var) : (nb073_alpha_dummy_019 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_019, fv_syn_c0] using (nb073_compact_fv_empty_0019 x y)

theorem nb073_wpp_notmem_0056 : (nb073_alpha_dummy_007) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_007, fv_syn_c0] using (nb073_compact_fv_empty_0020)

theorem nb073_wpp_notmem_0057 (x : Var) (y : Var) : (nb073_alpha_dummy_009 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_009, fv_syn_c0] using (nb073_compact_fv_empty_0021 x y)

theorem nb073_wpp_notmem_0058 : (nb073_alpha_dummy_006) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_006, fv_syn_c0] using (nb073_compact_fv_empty_0022)

theorem nb073_wpp_notmem_0059 (x : Var) (y : Var) : (nb073_alpha_dummy_008 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_008, fv_syn_c0] using (nb073_compact_fv_empty_0023 x y)

theorem nb073_wpp_notmem_0060 : (nb073_alpha_dummy_012) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_012, fv_syn_c0] using (nb073_compact_fv_empty_0024)

theorem nb073_wpp_notmem_0061 (x : Var) (y : Var) : (nb073_alpha_dummy_013 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_013, fv_syn_c0] using (nb073_compact_fv_empty_0025 x y)

theorem nb073_wpp_notmem_0062 : (nb073_alpha_dummy_010) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_010, fv_syn_c0] using (nb073_compact_fv_empty_0026)

theorem nb073_wpp_notmem_0063 (x : Var) (y : Var) : (nb073_alpha_dummy_011 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_011, fv_syn_c0] using (nb073_compact_fv_empty_0027 x y)

theorem nb073_wpp_notmem_0064 : (nb073_alpha_dummy_002) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_002, fv_syn_c0] using (nb073_compact_fv_empty_0028)

theorem nb073_wpp_notmem_0065 (x : Var) (y : Var) : (nb073_alpha_dummy_003 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_003, fv_syn_c0] using (nb073_compact_fv_empty_0029 x y)

theorem nb073_wpp_notmem_0066 : (nb073_alpha_dummy_001) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_001, fv_syn_c0] using (nb073_compact_fv_empty_0030)

theorem nb073_wpp_notmem_0067 (y : Var) : y ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb073_compact_fv_empty_0031 y)

theorem nb073_wpp_notmem_0068 : (nb073_alpha_dummy_000) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_000, fv_syn_c0] using (nb073_compact_fv_empty_0032)

theorem nb073_wpp_notmem_0069 (x : Var) : x ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb073_compact_fv_empty_0033 x)

theorem nb073_wpp_notmem_0070 : (nb073_alpha_dummy_004) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_004, fv_syn_c0] using (nb073_compact_fv_empty_0034)

theorem nb073_wpp_notmem_0071 (x : Var) (y : Var) : (nb073_alpha_dummy_005 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_005, fv_syn_c0] using (nb073_compact_fv_empty_0035 x y)

theorem nb073_compact_envfresh_0001 (x : Var) (y : Var) : TEnvFresh [((nb073_alpha_dummy_030), (nb073_alpha_dummy_033 x y)), ((nb073_alpha_dummy_029), (nb073_alpha_dummy_032 x y)), ((nb073_alpha_dummy_028), (nb073_alpha_dummy_031 x y)), ((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)), ((nb073_alpha_dummy_022), (nb073_alpha_dummy_024 x y)), ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)), ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_020), (nb073_alpha_dummy_021 x y)), ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)), ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb073_alpha_dummy_030) (nb073_alpha_dummy_033 x y) (nb073_wpp_notmem_0036) (nb073_wpp_notmem_0037 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_029) (nb073_alpha_dummy_032 x y) (nb073_wpp_notmem_0038) (nb073_wpp_notmem_0039 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_028) (nb073_alpha_dummy_031 x y) (nb073_wpp_notmem_0040) (nb073_wpp_notmem_0041 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_026) (nb073_alpha_dummy_027 x y) (nb073_wpp_notmem_0042) (nb073_wpp_notmem_0043 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_022) (nb073_alpha_dummy_024 x y) (nb073_wpp_notmem_0044) (nb073_wpp_notmem_0045 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_023) (nb073_alpha_dummy_025 x y) (nb073_wpp_notmem_0046) (nb073_wpp_notmem_0047 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_015) (nb073_alpha_dummy_017 x y) (nb073_wpp_notmem_0048) (nb073_wpp_notmem_0049 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_014) (nb073_alpha_dummy_016 x y) (nb073_wpp_notmem_0050) (nb073_wpp_notmem_0051 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_020) (nb073_alpha_dummy_021 x y) (nb073_wpp_notmem_0052) (nb073_wpp_notmem_0053 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_018) (nb073_alpha_dummy_019 x y) (nb073_wpp_notmem_0054) (nb073_wpp_notmem_0055 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_007) (nb073_alpha_dummy_009 x y) (nb073_wpp_notmem_0056) (nb073_wpp_notmem_0057 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_006) (nb073_alpha_dummy_008 x y) (nb073_wpp_notmem_0058) (nb073_wpp_notmem_0059 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_012) (nb073_alpha_dummy_013 x y) (nb073_wpp_notmem_0060) (nb073_wpp_notmem_0061 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_010) (nb073_alpha_dummy_011 x y) (nb073_wpp_notmem_0062) (nb073_wpp_notmem_0063 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_002) (nb073_alpha_dummy_003 x y) (nb073_wpp_notmem_0064) (nb073_wpp_notmem_0065 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_001) y (nb073_wpp_notmem_0066) (nb073_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb073_alpha_dummy_000) x (nb073_wpp_notmem_0068) (nb073_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb073_alpha_dummy_004) (nb073_alpha_dummy_005 x y) (nb073_wpp_notmem_0070) (nb073_wpp_notmem_0071 x y) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))

noncomputable def nb073_wpp_refl_0001 (x : Var) (y : Var) : TReflOn [((nb073_alpha_dummy_030), (nb073_alpha_dummy_033 x y)), ((nb073_alpha_dummy_029), (nb073_alpha_dummy_032 x y)), ((nb073_alpha_dummy_028), (nb073_alpha_dummy_031 x y)), ((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)), ((nb073_alpha_dummy_022), (nb073_alpha_dummy_024 x y)), ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)), ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_020), (nb073_alpha_dummy_021 x y)), ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)), ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb073_compact_envfresh_0001 x y)

theorem nb073_wpp_notmem_0072 : (nb073_alpha_dummy_026) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_026, fv_syn_cnnc] using (nb073_compact_fv_empty_0006)

theorem nb073_wpp_notmem_0073 (x : Var) (y : Var) : (nb073_alpha_dummy_027 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_027, fv_syn_cnnc] using (nb073_compact_fv_empty_0007 x y)

theorem nb073_wpp_notmem_0074 : (nb073_alpha_dummy_022) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_022, fv_syn_cnnc] using (nb073_compact_fv_empty_0008)

theorem nb073_wpp_notmem_0075 (x : Var) (y : Var) : (nb073_alpha_dummy_024 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_024, fv_syn_cnnc] using (nb073_compact_fv_empty_0009 x y)

theorem nb073_wpp_notmem_0076 : (nb073_alpha_dummy_023) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_023, fv_syn_cnnc] using (nb073_compact_fv_empty_0010)

theorem nb073_wpp_notmem_0077 (x : Var) (y : Var) : (nb073_alpha_dummy_025 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_025, fv_syn_cnnc] using (nb073_compact_fv_empty_0011 x y)

theorem nb073_wpp_notmem_0078 : (nb073_alpha_dummy_015) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_015, fv_syn_cnnc] using (nb073_compact_fv_empty_0012)

theorem nb073_wpp_notmem_0079 (x : Var) (y : Var) : (nb073_alpha_dummy_017 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_017, fv_syn_cnnc] using (nb073_compact_fv_empty_0013 x y)

theorem nb073_wpp_notmem_0080 : (nb073_alpha_dummy_014) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_014, fv_syn_cnnc] using (nb073_compact_fv_empty_0014)

theorem nb073_wpp_notmem_0081 (x : Var) (y : Var) : (nb073_alpha_dummy_016 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_016, fv_syn_cnnc] using (nb073_compact_fv_empty_0015 x y)

theorem nb073_wpp_notmem_0082 : (nb073_alpha_dummy_020) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_020, fv_syn_cnnc] using (nb073_compact_fv_empty_0016)

theorem nb073_wpp_notmem_0083 (x : Var) (y : Var) : (nb073_alpha_dummy_021 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_021, fv_syn_cnnc] using (nb073_compact_fv_empty_0017 x y)

theorem nb073_wpp_notmem_0084 : (nb073_alpha_dummy_018) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_018, fv_syn_cnnc] using (nb073_compact_fv_empty_0018)

theorem nb073_wpp_notmem_0085 (x : Var) (y : Var) : (nb073_alpha_dummy_019 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_019, fv_syn_cnnc] using (nb073_compact_fv_empty_0019 x y)

theorem nb073_wpp_notmem_0086 : (nb073_alpha_dummy_007) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_007, fv_syn_cnnc] using (nb073_compact_fv_empty_0020)

theorem nb073_wpp_notmem_0087 (x : Var) (y : Var) : (nb073_alpha_dummy_009 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_009, fv_syn_cnnc] using (nb073_compact_fv_empty_0021 x y)

theorem nb073_wpp_notmem_0088 : (nb073_alpha_dummy_006) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_006, fv_syn_cnnc] using (nb073_compact_fv_empty_0022)

theorem nb073_wpp_notmem_0089 (x : Var) (y : Var) : (nb073_alpha_dummy_008 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_008, fv_syn_cnnc] using (nb073_compact_fv_empty_0023 x y)

theorem nb073_wpp_notmem_0090 : (nb073_alpha_dummy_012) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_012, fv_syn_cnnc] using (nb073_compact_fv_empty_0024)

theorem nb073_wpp_notmem_0091 (x : Var) (y : Var) : (nb073_alpha_dummy_013 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_013, fv_syn_cnnc] using (nb073_compact_fv_empty_0025 x y)

theorem nb073_wpp_notmem_0092 : (nb073_alpha_dummy_010) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_010, fv_syn_cnnc] using (nb073_compact_fv_empty_0026)

theorem nb073_wpp_notmem_0093 (x : Var) (y : Var) : (nb073_alpha_dummy_011 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_011, fv_syn_cnnc] using (nb073_compact_fv_empty_0027 x y)

theorem nb073_wpp_notmem_0094 : (nb073_alpha_dummy_002) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_002, fv_syn_cnnc] using (nb073_compact_fv_empty_0028)

theorem nb073_wpp_notmem_0095 (x : Var) (y : Var) : (nb073_alpha_dummy_003 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_003, fv_syn_cnnc] using (nb073_compact_fv_empty_0029 x y)

theorem nb073_wpp_notmem_0096 : (nb073_alpha_dummy_001) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_001, fv_syn_cnnc] using (nb073_compact_fv_empty_0030)

theorem nb073_wpp_notmem_0097 (y : Var) : y ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb073_compact_fv_empty_0031 y)

theorem nb073_wpp_notmem_0098 : (nb073_alpha_dummy_000) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_000, fv_syn_cnnc] using (nb073_compact_fv_empty_0032)

theorem nb073_wpp_notmem_0099 (x : Var) : x ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb073_compact_fv_empty_0033 x)

theorem nb073_wpp_notmem_0100 : (nb073_alpha_dummy_004) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_004, fv_syn_cnnc] using (nb073_compact_fv_empty_0034)

theorem nb073_wpp_notmem_0101 (x : Var) (y : Var) : (nb073_alpha_dummy_005 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_005, fv_syn_cnnc] using (nb073_compact_fv_empty_0035 x y)

theorem nb073_compact_envfresh_0002 (x : Var) (y : Var) : TEnvFresh [((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)), ((nb073_alpha_dummy_022), (nb073_alpha_dummy_024 x y)), ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)), ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_020), (nb073_alpha_dummy_021 x y)), ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)), ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb073_alpha_dummy_026) (nb073_alpha_dummy_027 x y) (nb073_wpp_notmem_0072) (nb073_wpp_notmem_0073 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_022) (nb073_alpha_dummy_024 x y) (nb073_wpp_notmem_0074) (nb073_wpp_notmem_0075 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_023) (nb073_alpha_dummy_025 x y) (nb073_wpp_notmem_0076) (nb073_wpp_notmem_0077 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_015) (nb073_alpha_dummy_017 x y) (nb073_wpp_notmem_0078) (nb073_wpp_notmem_0079 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_014) (nb073_alpha_dummy_016 x y) (nb073_wpp_notmem_0080) (nb073_wpp_notmem_0081 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_020) (nb073_alpha_dummy_021 x y) (nb073_wpp_notmem_0082) (nb073_wpp_notmem_0083 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_018) (nb073_alpha_dummy_019 x y) (nb073_wpp_notmem_0084) (nb073_wpp_notmem_0085 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_007) (nb073_alpha_dummy_009 x y) (nb073_wpp_notmem_0086) (nb073_wpp_notmem_0087 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_006) (nb073_alpha_dummy_008 x y) (nb073_wpp_notmem_0088) (nb073_wpp_notmem_0089 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_012) (nb073_alpha_dummy_013 x y) (nb073_wpp_notmem_0090) (nb073_wpp_notmem_0091 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_010) (nb073_alpha_dummy_011 x y) (nb073_wpp_notmem_0092) (nb073_wpp_notmem_0093 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_002) (nb073_alpha_dummy_003 x y) (nb073_wpp_notmem_0094) (nb073_wpp_notmem_0095 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_001) y (nb073_wpp_notmem_0096) (nb073_wpp_notmem_0097 y) (TEnvFresh.consFresh (nb073_alpha_dummy_000) x (nb073_wpp_notmem_0098) (nb073_wpp_notmem_0099 x) (TEnvFresh.consFresh (nb073_alpha_dummy_004) (nb073_alpha_dummy_005 x y) (nb073_wpp_notmem_0100) (nb073_wpp_notmem_0101 x y) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))

noncomputable def nb073_wpp_refl_0002 (x : Var) (y : Var) : TReflOn [((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)), ((nb073_alpha_dummy_022), (nb073_alpha_dummy_024 x y)), ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)), ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_020), (nb073_alpha_dummy_021 x y)), ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)), ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb073_compact_envfresh_0002 x y)

noncomputable def nb073_split_alpha_0000 (x : Var) (y : Var) (dv_x_y : x ≠ y) : TAlphaWff [((nb073_alpha_dummy_020), (nb073_alpha_dummy_021 x y)), ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)), ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] (Wff.imp (Wff.classMem (Class.cv (nb073_alpha_dummy_020)) (Class.cab (nb073_alpha_dummy_014) (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_000)) (Wff.classEq (Class.cv (nb073_alpha_dummy_014)) (syn_cphi (Class.cv (nb073_alpha_dummy_015))))))) (Wff.neg (Wff.classMem (Class.cv (nb073_alpha_dummy_020)) (Class.cab (nb073_alpha_dummy_014) (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_000)) (Wff.classEq (Class.cv (nb073_alpha_dummy_014)) (syn_cphi (Class.cv (nb073_alpha_dummy_015))))))))) (Wff.imp (Wff.classMem (Class.cv (nb073_alpha_dummy_021 x y)) (Class.cab (nb073_alpha_dummy_016 x y) (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y))))))) (Wff.neg (Wff.classMem (Class.cv (nb073_alpha_dummy_021 x y)) (Class.cab (nb073_alpha_dummy_016 x y) (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0014) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0016 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0016 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0019 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0015) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0017 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0008) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0010 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0008) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0010 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0013 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0009) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0011 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0006) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0007 x y) 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_000))).fv ∪ ((Class.cv (nb073_alpha_dummy_001))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0021 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0020) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0021 x y) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_015))).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_017 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0024) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0025 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0025 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0023 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb073_alpha_dummy_030), (nb073_alpha_dummy_033 x y)), ((nb073_alpha_dummy_029), (nb073_alpha_dummy_032 x y)), ((nb073_alpha_dummy_028), (nb073_alpha_dummy_031 x y)), ((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)), ((nb073_alpha_dummy_022), (nb073_alpha_dummy_024 x y)), ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)), ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_020), (nb073_alpha_dummy_021 x y)), ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)), ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] (syn_c1c) (nb073_wpp_refl_0000 x y))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0029 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0027 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0033 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0031 x y) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0029 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0027 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0033 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0031 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb073_alpha_dummy_030), (nb073_alpha_dummy_033 x y)), ((nb073_alpha_dummy_029), (nb073_alpha_dummy_032 x y)), ((nb073_alpha_dummy_028), (nb073_alpha_dummy_031 x y)), ((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)), ((nb073_alpha_dummy_022), (nb073_alpha_dummy_024 x y)), ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)), ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_020), (nb073_alpha_dummy_021 x y)), ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)), ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] (syn_c0) (nb073_wpp_refl_0001 x y))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0036) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0037 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0034) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0035 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0036) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0037 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0034) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0035 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0040) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0041 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0038) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0039 x y) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0040) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0041 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0038) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0039 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0023 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)), ((nb073_alpha_dummy_022), (nb073_alpha_dummy_024 x y)), ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)), ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_020), (nb073_alpha_dummy_021 x y)), ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)), ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] (syn_cnnc) (nb073_wpp_refl_0002 x y))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0023 x y) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0023 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)), ((nb073_alpha_dummy_022), (nb073_alpha_dummy_024 x y)), ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)), ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_020), (nb073_alpha_dummy_021 x y)), ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)), ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] (syn_cnnc) (nb073_wpp_refl_0002 x y)))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0014) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0016 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0016 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0019 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0015) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0017 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0008) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0010 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0008) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0010 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0013 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0009) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0011 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0006) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0007 x y) 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_000))).fv ∪ ((Class.cv (nb073_alpha_dummy_001))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0021 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0020) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0021 x y) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_015))).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_017 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0024) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0025 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0025 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0023 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb073_alpha_dummy_030), (nb073_alpha_dummy_033 x y)), ((nb073_alpha_dummy_029), (nb073_alpha_dummy_032 x y)), ((nb073_alpha_dummy_028), (nb073_alpha_dummy_031 x y)), ((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)), ((nb073_alpha_dummy_022), (nb073_alpha_dummy_024 x y)), ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)), ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_020), (nb073_alpha_dummy_021 x y)), ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)), ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] (syn_c1c) (nb073_wpp_refl_0000 x y))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0029 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0027 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0033 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0031 x y) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0029 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0027 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0033 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0031 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb073_alpha_dummy_030), (nb073_alpha_dummy_033 x y)), ((nb073_alpha_dummy_029), (nb073_alpha_dummy_032 x y)), ((nb073_alpha_dummy_028), (nb073_alpha_dummy_031 x y)), ((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)), ((nb073_alpha_dummy_022), (nb073_alpha_dummy_024 x y)), ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)), ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_020), (nb073_alpha_dummy_021 x y)), ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)), ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] (syn_c0) (nb073_wpp_refl_0001 x y))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0036) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0037 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0034) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0035 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0036) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0037 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0034) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0035 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0040) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0041 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0038) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0039 x y) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0040) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0041 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0038) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0039 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0023 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)), ((nb073_alpha_dummy_022), (nb073_alpha_dummy_024 x y)), ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)), ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_020), (nb073_alpha_dummy_021 x y)), ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)), ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] (syn_cnnc) (nb073_wpp_refl_0002 x y))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0023 x y) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0023 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)), ((nb073_alpha_dummy_022), (nb073_alpha_dummy_024 x y)), ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)), ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_020), (nb073_alpha_dummy_021 x y)), ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)), ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] (syn_cnnc) (nb073_wpp_refl_0002 x y))))))))))))))))))))))))))))

theorem nb073_compact_fv_empty_0036 : (nb073_alpha_dummy_048) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0102 : (nb073_alpha_dummy_048) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_048, fv_syn_c1c] using (nb073_compact_fv_empty_0036)

theorem nb073_compact_fv_empty_0037 (x : Var) (y : Var) : (nb073_alpha_dummy_049 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0103 (x : Var) (y : Var) : (nb073_alpha_dummy_049 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_049, fv_syn_c1c] using (nb073_compact_fv_empty_0037 x y)

theorem nb073_compact_fv_empty_0038 : (nb073_alpha_dummy_046) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0104 : (nb073_alpha_dummy_046) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_046, fv_syn_c1c] using (nb073_compact_fv_empty_0038)

theorem nb073_compact_fv_empty_0039 (x : Var) (y : Var) : (nb073_alpha_dummy_047 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0105 (x : Var) (y : Var) : (nb073_alpha_dummy_047 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_047, fv_syn_c1c] using (nb073_compact_fv_empty_0039 x y)

theorem nb073_compact_fv_empty_0040 : (nb073_alpha_dummy_044) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0106 : (nb073_alpha_dummy_044) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_044, fv_syn_c1c] using (nb073_compact_fv_empty_0040)

theorem nb073_compact_fv_empty_0041 (x : Var) (y : Var) : (nb073_alpha_dummy_045 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0107 (x : Var) (y : Var) : (nb073_alpha_dummy_045 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_045, fv_syn_c1c] using (nb073_compact_fv_empty_0041 x y)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
