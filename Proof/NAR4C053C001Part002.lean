import NAR4C053C001Part001

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

theorem nb053_wpp_notmem_0004 : (nb053_alpha_dummy_018) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_018, fv_syn_c1c] using (nb053_compact_fv_empty_0004)

theorem nb053_compact_fv_empty_0005 (x : Var) (y : Var) : (nb053_alpha_dummy_021 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0005 (x : Var) (y : Var) : (nb053_alpha_dummy_021 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_021, fv_syn_c1c] using (nb053_compact_fv_empty_0005 x y)

theorem nb053_compact_fv_empty_0006 : (nb053_alpha_dummy_016) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0006 : (nb053_alpha_dummy_016) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_016, fv_syn_c1c] using (nb053_compact_fv_empty_0006)

theorem nb053_compact_fv_empty_0007 (x : Var) (y : Var) : (nb053_alpha_dummy_017 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0007 (x : Var) (y : Var) : (nb053_alpha_dummy_017 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_017, fv_syn_c1c] using (nb053_compact_fv_empty_0007 x y)

theorem nb053_compact_fv_empty_0008 : (nb053_alpha_dummy_012) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0008 : (nb053_alpha_dummy_012) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_012, fv_syn_c1c] using (nb053_compact_fv_empty_0008)

theorem nb053_compact_fv_empty_0009 (x : Var) (y : Var) : (nb053_alpha_dummy_014 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0009 (x : Var) (y : Var) : (nb053_alpha_dummy_014 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_014, fv_syn_c1c] using (nb053_compact_fv_empty_0009 x y)

theorem nb053_compact_fv_empty_0010 : (nb053_alpha_dummy_013) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0010 : (nb053_alpha_dummy_013) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_013, fv_syn_c1c] using (nb053_compact_fv_empty_0010)

theorem nb053_compact_fv_empty_0011 (x : Var) (y : Var) : (nb053_alpha_dummy_015 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0011 (x : Var) (y : Var) : (nb053_alpha_dummy_015 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_015, fv_syn_c1c] using (nb053_compact_fv_empty_0011 x y)

theorem nb053_compact_fv_empty_0012 : (nb053_alpha_dummy_005) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0012 : (nb053_alpha_dummy_005) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_005, fv_syn_c1c] using (nb053_compact_fv_empty_0012)

theorem nb053_compact_fv_empty_0013 (x : Var) (y : Var) : (nb053_alpha_dummy_007 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0013 (x : Var) (y : Var) : (nb053_alpha_dummy_007 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_007, fv_syn_c1c] using (nb053_compact_fv_empty_0013 x y)

theorem nb053_compact_fv_empty_0014 : (nb053_alpha_dummy_004) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0014 : (nb053_alpha_dummy_004) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_004, fv_syn_c1c] using (nb053_compact_fv_empty_0014)

theorem nb053_compact_fv_empty_0015 (x : Var) (y : Var) : (nb053_alpha_dummy_006 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0015 (x : Var) (y : Var) : (nb053_alpha_dummy_006 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_006, fv_syn_c1c] using (nb053_compact_fv_empty_0015 x y)

theorem nb053_compact_fv_empty_0016 : (nb053_alpha_dummy_010) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0016 : (nb053_alpha_dummy_010) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_010, fv_syn_c1c] using (nb053_compact_fv_empty_0016)

theorem nb053_compact_fv_empty_0017 (x : Var) (y : Var) : (nb053_alpha_dummy_011 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0017 (x : Var) (y : Var) : (nb053_alpha_dummy_011 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_011, fv_syn_c1c] using (nb053_compact_fv_empty_0017 x y)

theorem nb053_compact_fv_empty_0018 : (nb053_alpha_dummy_008) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0018 : (nb053_alpha_dummy_008) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_008, fv_syn_c1c] using (nb053_compact_fv_empty_0018)

theorem nb053_compact_fv_empty_0019 (x : Var) (y : Var) : (nb053_alpha_dummy_009 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0019 (x : Var) (y : Var) : (nb053_alpha_dummy_009 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_009, fv_syn_c1c] using (nb053_compact_fv_empty_0019 x y)

theorem nb053_compact_fv_empty_0020 : (nb053_alpha_dummy_001) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0020 : (nb053_alpha_dummy_001) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_001, fv_syn_c1c] using (nb053_compact_fv_empty_0020)

theorem nb053_compact_fv_empty_0021 (y : Var) : y ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0021 (y : Var) : y ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb053_compact_fv_empty_0021 y)

theorem nb053_compact_fv_empty_0022 : (nb053_alpha_dummy_000) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0022 : (nb053_alpha_dummy_000) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_000, fv_syn_c1c] using (nb053_compact_fv_empty_0022)

theorem nb053_compact_fv_empty_0023 (x : Var) : x ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0023 (x : Var) : x ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb053_compact_fv_empty_0023 x)

theorem nb053_compact_fv_empty_0024 : (nb053_alpha_dummy_002) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0024 : (nb053_alpha_dummy_002) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_002, fv_syn_c1c] using (nb053_compact_fv_empty_0024)

theorem nb053_compact_fv_empty_0025 (x : Var) (y : Var) : (nb053_alpha_dummy_003 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0025 (x : Var) (y : Var) : (nb053_alpha_dummy_003 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_003, fv_syn_c1c] using (nb053_compact_fv_empty_0025 x y)

theorem nb053_compact_envfresh_0000 (x : Var) (y : Var) : TEnvFresh [((nb053_alpha_dummy_020), (nb053_alpha_dummy_023 x y)), ((nb053_alpha_dummy_019), (nb053_alpha_dummy_022 x y)), ((nb053_alpha_dummy_018), (nb053_alpha_dummy_021 x y)), ((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)), ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)), ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)), ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)), ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)), ((nb053_alpha_dummy_010), (nb053_alpha_dummy_011 x y)), ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)), ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb053_alpha_dummy_020) (nb053_alpha_dummy_023 x y) (nb053_wpp_notmem_0000) (nb053_wpp_notmem_0001 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_019) (nb053_alpha_dummy_022 x y) (nb053_wpp_notmem_0002) (nb053_wpp_notmem_0003 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_018) (nb053_alpha_dummy_021 x y) (nb053_wpp_notmem_0004) (nb053_wpp_notmem_0005 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_016) (nb053_alpha_dummy_017 x y) (nb053_wpp_notmem_0006) (nb053_wpp_notmem_0007 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_012) (nb053_alpha_dummy_014 x y) (nb053_wpp_notmem_0008) (nb053_wpp_notmem_0009 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_013) (nb053_alpha_dummy_015 x y) (nb053_wpp_notmem_0010) (nb053_wpp_notmem_0011 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_005) (nb053_alpha_dummy_007 x y) (nb053_wpp_notmem_0012) (nb053_wpp_notmem_0013 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_004) (nb053_alpha_dummy_006 x y) (nb053_wpp_notmem_0014) (nb053_wpp_notmem_0015 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_010) (nb053_alpha_dummy_011 x y) (nb053_wpp_notmem_0016) (nb053_wpp_notmem_0017 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_008) (nb053_alpha_dummy_009 x y) (nb053_wpp_notmem_0018) (nb053_wpp_notmem_0019 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_001) y (nb053_wpp_notmem_0020) (nb053_wpp_notmem_0021 y) (TEnvFresh.consFresh (nb053_alpha_dummy_000) x (nb053_wpp_notmem_0022) (nb053_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb053_alpha_dummy_002) (nb053_alpha_dummy_003 x y) (nb053_wpp_notmem_0024) (nb053_wpp_notmem_0025 x y) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))

noncomputable def nb053_wpp_refl_0000 (x : Var) (y : Var) : TReflOn [((nb053_alpha_dummy_020), (nb053_alpha_dummy_023 x y)), ((nb053_alpha_dummy_019), (nb053_alpha_dummy_022 x y)), ((nb053_alpha_dummy_018), (nb053_alpha_dummy_021 x y)), ((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)), ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)), ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)), ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)), ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)), ((nb053_alpha_dummy_010), (nb053_alpha_dummy_011 x y)), ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)), ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb053_compact_envfresh_0000 x y)

theorem nb053_wpp_notmem_0026 : (nb053_alpha_dummy_020) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_020, fv_syn_c0] using (nb053_compact_fv_empty_0000)

theorem nb053_wpp_notmem_0027 (x : Var) (y : Var) : (nb053_alpha_dummy_023 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_023, fv_syn_c0] using (nb053_compact_fv_empty_0001 x y)

theorem nb053_wpp_notmem_0028 : (nb053_alpha_dummy_019) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_019, fv_syn_c0] using (nb053_compact_fv_empty_0002)

theorem nb053_wpp_notmem_0029 (x : Var) (y : Var) : (nb053_alpha_dummy_022 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_022, fv_syn_c0] using (nb053_compact_fv_empty_0003 x y)

theorem nb053_wpp_notmem_0030 : (nb053_alpha_dummy_018) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_018, fv_syn_c0] using (nb053_compact_fv_empty_0004)

theorem nb053_wpp_notmem_0031 (x : Var) (y : Var) : (nb053_alpha_dummy_021 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_021, fv_syn_c0] using (nb053_compact_fv_empty_0005 x y)

theorem nb053_wpp_notmem_0032 : (nb053_alpha_dummy_016) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_016, fv_syn_c0] using (nb053_compact_fv_empty_0006)

theorem nb053_wpp_notmem_0033 (x : Var) (y : Var) : (nb053_alpha_dummy_017 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_017, fv_syn_c0] using (nb053_compact_fv_empty_0007 x y)

theorem nb053_wpp_notmem_0034 : (nb053_alpha_dummy_012) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_012, fv_syn_c0] using (nb053_compact_fv_empty_0008)

theorem nb053_wpp_notmem_0035 (x : Var) (y : Var) : (nb053_alpha_dummy_014 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_014, fv_syn_c0] using (nb053_compact_fv_empty_0009 x y)

theorem nb053_wpp_notmem_0036 : (nb053_alpha_dummy_013) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_013, fv_syn_c0] using (nb053_compact_fv_empty_0010)

theorem nb053_wpp_notmem_0037 (x : Var) (y : Var) : (nb053_alpha_dummy_015 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_015, fv_syn_c0] using (nb053_compact_fv_empty_0011 x y)

theorem nb053_wpp_notmem_0038 : (nb053_alpha_dummy_005) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_005, fv_syn_c0] using (nb053_compact_fv_empty_0012)

theorem nb053_wpp_notmem_0039 (x : Var) (y : Var) : (nb053_alpha_dummy_007 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_007, fv_syn_c0] using (nb053_compact_fv_empty_0013 x y)

theorem nb053_wpp_notmem_0040 : (nb053_alpha_dummy_004) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_004, fv_syn_c0] using (nb053_compact_fv_empty_0014)

theorem nb053_wpp_notmem_0041 (x : Var) (y : Var) : (nb053_alpha_dummy_006 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_006, fv_syn_c0] using (nb053_compact_fv_empty_0015 x y)

theorem nb053_wpp_notmem_0042 : (nb053_alpha_dummy_010) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_010, fv_syn_c0] using (nb053_compact_fv_empty_0016)

theorem nb053_wpp_notmem_0043 (x : Var) (y : Var) : (nb053_alpha_dummy_011 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_011, fv_syn_c0] using (nb053_compact_fv_empty_0017 x y)

theorem nb053_wpp_notmem_0044 : (nb053_alpha_dummy_008) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_008, fv_syn_c0] using (nb053_compact_fv_empty_0018)

theorem nb053_wpp_notmem_0045 (x : Var) (y : Var) : (nb053_alpha_dummy_009 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_009, fv_syn_c0] using (nb053_compact_fv_empty_0019 x y)

theorem nb053_wpp_notmem_0046 : (nb053_alpha_dummy_001) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_001, fv_syn_c0] using (nb053_compact_fv_empty_0020)

theorem nb053_wpp_notmem_0047 (y : Var) : y ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb053_compact_fv_empty_0021 y)

theorem nb053_wpp_notmem_0048 : (nb053_alpha_dummy_000) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_000, fv_syn_c0] using (nb053_compact_fv_empty_0022)

theorem nb053_wpp_notmem_0049 (x : Var) : x ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb053_compact_fv_empty_0023 x)

theorem nb053_wpp_notmem_0050 : (nb053_alpha_dummy_002) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_002, fv_syn_c0] using (nb053_compact_fv_empty_0024)

theorem nb053_wpp_notmem_0051 (x : Var) (y : Var) : (nb053_alpha_dummy_003 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_003, fv_syn_c0] using (nb053_compact_fv_empty_0025 x y)

theorem nb053_compact_envfresh_0001 (x : Var) (y : Var) : TEnvFresh [((nb053_alpha_dummy_020), (nb053_alpha_dummy_023 x y)), ((nb053_alpha_dummy_019), (nb053_alpha_dummy_022 x y)), ((nb053_alpha_dummy_018), (nb053_alpha_dummy_021 x y)), ((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)), ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)), ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)), ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)), ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)), ((nb053_alpha_dummy_010), (nb053_alpha_dummy_011 x y)), ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)), ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb053_alpha_dummy_020) (nb053_alpha_dummy_023 x y) (nb053_wpp_notmem_0026) (nb053_wpp_notmem_0027 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_019) (nb053_alpha_dummy_022 x y) (nb053_wpp_notmem_0028) (nb053_wpp_notmem_0029 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_018) (nb053_alpha_dummy_021 x y) (nb053_wpp_notmem_0030) (nb053_wpp_notmem_0031 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_016) (nb053_alpha_dummy_017 x y) (nb053_wpp_notmem_0032) (nb053_wpp_notmem_0033 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_012) (nb053_alpha_dummy_014 x y) (nb053_wpp_notmem_0034) (nb053_wpp_notmem_0035 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_013) (nb053_alpha_dummy_015 x y) (nb053_wpp_notmem_0036) (nb053_wpp_notmem_0037 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_005) (nb053_alpha_dummy_007 x y) (nb053_wpp_notmem_0038) (nb053_wpp_notmem_0039 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_004) (nb053_alpha_dummy_006 x y) (nb053_wpp_notmem_0040) (nb053_wpp_notmem_0041 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_010) (nb053_alpha_dummy_011 x y) (nb053_wpp_notmem_0042) (nb053_wpp_notmem_0043 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_008) (nb053_alpha_dummy_009 x y) (nb053_wpp_notmem_0044) (nb053_wpp_notmem_0045 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_001) y (nb053_wpp_notmem_0046) (nb053_wpp_notmem_0047 y) (TEnvFresh.consFresh (nb053_alpha_dummy_000) x (nb053_wpp_notmem_0048) (nb053_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb053_alpha_dummy_002) (nb053_alpha_dummy_003 x y) (nb053_wpp_notmem_0050) (nb053_wpp_notmem_0051 x y) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))

noncomputable def nb053_wpp_refl_0001 (x : Var) (y : Var) : TReflOn [((nb053_alpha_dummy_020), (nb053_alpha_dummy_023 x y)), ((nb053_alpha_dummy_019), (nb053_alpha_dummy_022 x y)), ((nb053_alpha_dummy_018), (nb053_alpha_dummy_021 x y)), ((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)), ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)), ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)), ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)), ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)), ((nb053_alpha_dummy_010), (nb053_alpha_dummy_011 x y)), ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)), ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb053_compact_envfresh_0001 x y)

noncomputable def nb053_split_alpha_0000 (x : Var) (y : Var) : TAlphaWff [((nb053_alpha_dummy_020), (nb053_alpha_dummy_023 x y)), ((nb053_alpha_dummy_019), (nb053_alpha_dummy_022 x y)), ((nb053_alpha_dummy_018), (nb053_alpha_dummy_021 x y)), ((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)), ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)), ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)), ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)), ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)), ((nb053_alpha_dummy_010), (nb053_alpha_dummy_011 x y)), ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)), ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb053_alpha_dummy_019)) (Class.cv (nb053_alpha_dummy_020))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb053_alpha_dummy_018)) (syn_cun (Class.cv (nb053_alpha_dummy_019)) (Class.cv (nb053_alpha_dummy_020)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb053_alpha_dummy_022 x y)) (Class.cv (nb053_alpha_dummy_023 x y))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb053_alpha_dummy_021 x y)) (syn_cun (Class.cv (nb053_alpha_dummy_022 x y)) (Class.cv (nb053_alpha_dummy_023 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0019 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0017 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0023 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0021 x y) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0019 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0017 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0023 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0021 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb053_alpha_dummy_020), (nb053_alpha_dummy_023 x y)), ((nb053_alpha_dummy_019), (nb053_alpha_dummy_022 x y)), ((nb053_alpha_dummy_018), (nb053_alpha_dummy_021 x y)), ((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)), ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)), ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)), ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)), ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)), ((nb053_alpha_dummy_010), (nb053_alpha_dummy_011 x y)), ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)), ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))] (syn_c0) (nb053_wpp_refl_0001 x y))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0027 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0025 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0027 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0025 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0031 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0029 x y) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0031 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0029 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb053_wpp_notmem_0052 : (nb053_alpha_dummy_016) ∉ ((syn_cnnc)).fv := by
  simpa only [nb053_alpha_dummy_016, fv_syn_cnnc] using (nb053_compact_fv_empty_0006)

theorem nb053_wpp_notmem_0053 (x : Var) (y : Var) : (nb053_alpha_dummy_017 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb053_alpha_dummy_017, fv_syn_cnnc] using (nb053_compact_fv_empty_0007 x y)

theorem nb053_wpp_notmem_0054 : (nb053_alpha_dummy_012) ∉ ((syn_cnnc)).fv := by
  simpa only [nb053_alpha_dummy_012, fv_syn_cnnc] using (nb053_compact_fv_empty_0008)

theorem nb053_wpp_notmem_0055 (x : Var) (y : Var) : (nb053_alpha_dummy_014 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb053_alpha_dummy_014, fv_syn_cnnc] using (nb053_compact_fv_empty_0009 x y)

theorem nb053_wpp_notmem_0056 : (nb053_alpha_dummy_013) ∉ ((syn_cnnc)).fv := by
  simpa only [nb053_alpha_dummy_013, fv_syn_cnnc] using (nb053_compact_fv_empty_0010)

theorem nb053_wpp_notmem_0057 (x : Var) (y : Var) : (nb053_alpha_dummy_015 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb053_alpha_dummy_015, fv_syn_cnnc] using (nb053_compact_fv_empty_0011 x y)

theorem nb053_wpp_notmem_0058 : (nb053_alpha_dummy_005) ∉ ((syn_cnnc)).fv := by
  simpa only [nb053_alpha_dummy_005, fv_syn_cnnc] using (nb053_compact_fv_empty_0012)

theorem nb053_wpp_notmem_0059 (x : Var) (y : Var) : (nb053_alpha_dummy_007 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb053_alpha_dummy_007, fv_syn_cnnc] using (nb053_compact_fv_empty_0013 x y)

theorem nb053_wpp_notmem_0060 : (nb053_alpha_dummy_004) ∉ ((syn_cnnc)).fv := by
  simpa only [nb053_alpha_dummy_004, fv_syn_cnnc] using (nb053_compact_fv_empty_0014)

theorem nb053_wpp_notmem_0061 (x : Var) (y : Var) : (nb053_alpha_dummy_006 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb053_alpha_dummy_006, fv_syn_cnnc] using (nb053_compact_fv_empty_0015 x y)

theorem nb053_wpp_notmem_0062 : (nb053_alpha_dummy_010) ∉ ((syn_cnnc)).fv := by
  simpa only [nb053_alpha_dummy_010, fv_syn_cnnc] using (nb053_compact_fv_empty_0016)

theorem nb053_wpp_notmem_0063 (x : Var) (y : Var) : (nb053_alpha_dummy_011 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb053_alpha_dummy_011, fv_syn_cnnc] using (nb053_compact_fv_empty_0017 x y)

theorem nb053_wpp_notmem_0064 : (nb053_alpha_dummy_008) ∉ ((syn_cnnc)).fv := by
  simpa only [nb053_alpha_dummy_008, fv_syn_cnnc] using (nb053_compact_fv_empty_0018)

theorem nb053_wpp_notmem_0065 (x : Var) (y : Var) : (nb053_alpha_dummy_009 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb053_alpha_dummy_009, fv_syn_cnnc] using (nb053_compact_fv_empty_0019 x y)

theorem nb053_wpp_notmem_0066 : (nb053_alpha_dummy_001) ∉ ((syn_cnnc)).fv := by
  simpa only [nb053_alpha_dummy_001, fv_syn_cnnc] using (nb053_compact_fv_empty_0020)

theorem nb053_wpp_notmem_0067 (y : Var) : y ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb053_compact_fv_empty_0021 y)

theorem nb053_wpp_notmem_0068 : (nb053_alpha_dummy_000) ∉ ((syn_cnnc)).fv := by
  simpa only [nb053_alpha_dummy_000, fv_syn_cnnc] using (nb053_compact_fv_empty_0022)

theorem nb053_wpp_notmem_0069 (x : Var) : x ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb053_compact_fv_empty_0023 x)

theorem nb053_wpp_notmem_0070 : (nb053_alpha_dummy_002) ∉ ((syn_cnnc)).fv := by
  simpa only [nb053_alpha_dummy_002, fv_syn_cnnc] using (nb053_compact_fv_empty_0024)

theorem nb053_wpp_notmem_0071 (x : Var) (y : Var) : (nb053_alpha_dummy_003 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb053_alpha_dummy_003, fv_syn_cnnc] using (nb053_compact_fv_empty_0025 x y)

theorem nb053_compact_envfresh_0002 (x : Var) (y : Var) : TEnvFresh [((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)), ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)), ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)), ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)), ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)), ((nb053_alpha_dummy_010), (nb053_alpha_dummy_011 x y)), ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)), ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb053_alpha_dummy_016) (nb053_alpha_dummy_017 x y) (nb053_wpp_notmem_0052) (nb053_wpp_notmem_0053 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_012) (nb053_alpha_dummy_014 x y) (nb053_wpp_notmem_0054) (nb053_wpp_notmem_0055 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_013) (nb053_alpha_dummy_015 x y) (nb053_wpp_notmem_0056) (nb053_wpp_notmem_0057 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_005) (nb053_alpha_dummy_007 x y) (nb053_wpp_notmem_0058) (nb053_wpp_notmem_0059 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_004) (nb053_alpha_dummy_006 x y) (nb053_wpp_notmem_0060) (nb053_wpp_notmem_0061 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_010) (nb053_alpha_dummy_011 x y) (nb053_wpp_notmem_0062) (nb053_wpp_notmem_0063 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_008) (nb053_alpha_dummy_009 x y) (nb053_wpp_notmem_0064) (nb053_wpp_notmem_0065 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_001) y (nb053_wpp_notmem_0066) (nb053_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb053_alpha_dummy_000) x (nb053_wpp_notmem_0068) (nb053_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb053_alpha_dummy_002) (nb053_alpha_dummy_003 x y) (nb053_wpp_notmem_0070) (nb053_wpp_notmem_0071 x y) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))

noncomputable def nb053_wpp_refl_0002 (x : Var) (y : Var) : TReflOn [((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)), ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)), ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)), ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)), ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)), ((nb053_alpha_dummy_010), (nb053_alpha_dummy_011 x y)), ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)), ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb053_compact_envfresh_0002 x y)

noncomputable def nb053_split_alpha_0001 (x : Var) (y : Var) (dv_x_y : x ≠ y) : TAlphaWff [((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)), ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)), ((nb053_alpha_dummy_010), (nb053_alpha_dummy_011 x y)), ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)), ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))] (Wff.imp (Wff.classMem (Class.cv (nb053_alpha_dummy_005)) (Class.cv (nb053_alpha_dummy_000))) (Wff.neg (Wff.classEq (Class.cv (nb053_alpha_dummy_004)) (syn_cphi (Class.cv (nb053_alpha_dummy_005)))))) (Wff.imp (Wff.classMem (Class.cv (nb053_alpha_dummy_007 x y)) (Class.cv x)) (Wff.neg (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y)) (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0004) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0006 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0004) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0006 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0008) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0009 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0005) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0007 x y) 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb053_alpha_dummy_000))).fv ∪ ((Class.cv (nb053_alpha_dummy_001))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0010) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0011 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0010) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0011 x y) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb053_alpha_dummy_005))).fv) (by decide)) (freshVar_injective (((Class.cv (nb053_alpha_dummy_007 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0014) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0015 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0015 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb053_alpha_dummy_020), (nb053_alpha_dummy_023 x y)), ((nb053_alpha_dummy_019), (nb053_alpha_dummy_022 x y)), ((nb053_alpha_dummy_018), (nb053_alpha_dummy_021 x y)), ((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)), ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)), ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)), ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)), ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)), ((nb053_alpha_dummy_010), (nb053_alpha_dummy_011 x y)), ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)), ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))] (syn_c1c) (nb053_wpp_refl_0000 x y))) (TAlphaWff.neg (TAlphaWff.neg (nb053_split_alpha_0000 x y)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)), ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)), ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)), ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)), ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)), ((nb053_alpha_dummy_010), (nb053_alpha_dummy_011 x y)), ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)), ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))] (syn_cnnc) (nb053_wpp_refl_0002 x y))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)), ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)), ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)), ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)), ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)), ((nb053_alpha_dummy_010), (nb053_alpha_dummy_011 x y)), ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)), ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))] (syn_cnnc) (nb053_wpp_refl_0002 x y))))))))))))))))))))

theorem nb053_compact_fv_empty_0026 : (nb053_alpha_dummy_038) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0072 : (nb053_alpha_dummy_038) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_038, fv_syn_c1c] using (nb053_compact_fv_empty_0026)

theorem nb053_compact_fv_empty_0027 (x : Var) (y : Var) : (nb053_alpha_dummy_039 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0073 (x : Var) (y : Var) : (nb053_alpha_dummy_039 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_039, fv_syn_c1c] using (nb053_compact_fv_empty_0027 x y)

theorem nb053_compact_fv_empty_0028 : (nb053_alpha_dummy_036) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0074 : (nb053_alpha_dummy_036) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_036, fv_syn_c1c] using (nb053_compact_fv_empty_0028)

theorem nb053_compact_fv_empty_0029 (x : Var) (y : Var) : (nb053_alpha_dummy_037 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0075 (x : Var) (y : Var) : (nb053_alpha_dummy_037 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_037, fv_syn_c1c] using (nb053_compact_fv_empty_0029 x y)

theorem nb053_compact_fv_empty_0030 : (nb053_alpha_dummy_034) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0076 : (nb053_alpha_dummy_034) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_034, fv_syn_c1c] using (nb053_compact_fv_empty_0030)

theorem nb053_compact_fv_empty_0031 (x : Var) (y : Var) : (nb053_alpha_dummy_035 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb053_wpp_notmem_0077 (x : Var) (y : Var) : (nb053_alpha_dummy_035 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb053_alpha_dummy_035, fv_syn_c1c] using (nb053_compact_fv_empty_0031 x y)

theorem nb053_compact_envfresh_0003 (x : Var) (y : Var) : TEnvFresh [((nb053_alpha_dummy_020), (nb053_alpha_dummy_023 x y)), ((nb053_alpha_dummy_019), (nb053_alpha_dummy_022 x y)), ((nb053_alpha_dummy_018), (nb053_alpha_dummy_021 x y)), ((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)), ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)), ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)), ((nb053_alpha_dummy_038), (nb053_alpha_dummy_039 x y)), ((nb053_alpha_dummy_036), (nb053_alpha_dummy_037 x y)), ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)), ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)), ((nb053_alpha_dummy_034), (nb053_alpha_dummy_035 x y)), ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)), ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb053_alpha_dummy_020) (nb053_alpha_dummy_023 x y) (nb053_wpp_notmem_0000) (nb053_wpp_notmem_0001 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_019) (nb053_alpha_dummy_022 x y) (nb053_wpp_notmem_0002) (nb053_wpp_notmem_0003 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_018) (nb053_alpha_dummy_021 x y) (nb053_wpp_notmem_0004) (nb053_wpp_notmem_0005 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_016) (nb053_alpha_dummy_017 x y) (nb053_wpp_notmem_0006) (nb053_wpp_notmem_0007 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_012) (nb053_alpha_dummy_014 x y) (nb053_wpp_notmem_0008) (nb053_wpp_notmem_0009 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_013) (nb053_alpha_dummy_015 x y) (nb053_wpp_notmem_0010) (nb053_wpp_notmem_0011 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_038) (nb053_alpha_dummy_039 x y) (nb053_wpp_notmem_0072) (nb053_wpp_notmem_0073 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_036) (nb053_alpha_dummy_037 x y) (nb053_wpp_notmem_0074) (nb053_wpp_notmem_0075 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_005) (nb053_alpha_dummy_007 x y) (nb053_wpp_notmem_0012) (nb053_wpp_notmem_0013 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_004) (nb053_alpha_dummy_006 x y) (nb053_wpp_notmem_0014) (nb053_wpp_notmem_0015 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_034) (nb053_alpha_dummy_035 x y) (nb053_wpp_notmem_0076) (nb053_wpp_notmem_0077 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_008) (nb053_alpha_dummy_009 x y) (nb053_wpp_notmem_0018) (nb053_wpp_notmem_0019 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_001) y (nb053_wpp_notmem_0020) (nb053_wpp_notmem_0021 y) (TEnvFresh.consFresh (nb053_alpha_dummy_000) x (nb053_wpp_notmem_0022) (nb053_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb053_alpha_dummy_002) (nb053_alpha_dummy_003 x y) (nb053_wpp_notmem_0024) (nb053_wpp_notmem_0025 x y) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb053_wpp_refl_0003 (x : Var) (y : Var) : TReflOn [((nb053_alpha_dummy_020), (nb053_alpha_dummy_023 x y)), ((nb053_alpha_dummy_019), (nb053_alpha_dummy_022 x y)), ((nb053_alpha_dummy_018), (nb053_alpha_dummy_021 x y)), ((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)), ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)), ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)), ((nb053_alpha_dummy_038), (nb053_alpha_dummy_039 x y)), ((nb053_alpha_dummy_036), (nb053_alpha_dummy_037 x y)), ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)), ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)), ((nb053_alpha_dummy_034), (nb053_alpha_dummy_035 x y)), ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)), ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb053_compact_envfresh_0003 x y)

theorem nb053_wpp_notmem_0078 : (nb053_alpha_dummy_038) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_038, fv_syn_c0] using (nb053_compact_fv_empty_0026)

theorem nb053_wpp_notmem_0079 (x : Var) (y : Var) : (nb053_alpha_dummy_039 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_039, fv_syn_c0] using (nb053_compact_fv_empty_0027 x y)

theorem nb053_wpp_notmem_0080 : (nb053_alpha_dummy_036) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_036, fv_syn_c0] using (nb053_compact_fv_empty_0028)

theorem nb053_wpp_notmem_0081 (x : Var) (y : Var) : (nb053_alpha_dummy_037 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_037, fv_syn_c0] using (nb053_compact_fv_empty_0029 x y)

theorem nb053_wpp_notmem_0082 : (nb053_alpha_dummy_034) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_034, fv_syn_c0] using (nb053_compact_fv_empty_0030)

theorem nb053_wpp_notmem_0083 (x : Var) (y : Var) : (nb053_alpha_dummy_035 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb053_alpha_dummy_035, fv_syn_c0] using (nb053_compact_fv_empty_0031 x y)

theorem nb053_compact_envfresh_0004 (x : Var) (y : Var) : TEnvFresh [((nb053_alpha_dummy_020), (nb053_alpha_dummy_023 x y)), ((nb053_alpha_dummy_019), (nb053_alpha_dummy_022 x y)), ((nb053_alpha_dummy_018), (nb053_alpha_dummy_021 x y)), ((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)), ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)), ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)), ((nb053_alpha_dummy_038), (nb053_alpha_dummy_039 x y)), ((nb053_alpha_dummy_036), (nb053_alpha_dummy_037 x y)), ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)), ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)), ((nb053_alpha_dummy_034), (nb053_alpha_dummy_035 x y)), ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)), ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb053_alpha_dummy_020) (nb053_alpha_dummy_023 x y) (nb053_wpp_notmem_0026) (nb053_wpp_notmem_0027 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_019) (nb053_alpha_dummy_022 x y) (nb053_wpp_notmem_0028) (nb053_wpp_notmem_0029 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_018) (nb053_alpha_dummy_021 x y) (nb053_wpp_notmem_0030) (nb053_wpp_notmem_0031 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_016) (nb053_alpha_dummy_017 x y) (nb053_wpp_notmem_0032) (nb053_wpp_notmem_0033 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_012) (nb053_alpha_dummy_014 x y) (nb053_wpp_notmem_0034) (nb053_wpp_notmem_0035 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_013) (nb053_alpha_dummy_015 x y) (nb053_wpp_notmem_0036) (nb053_wpp_notmem_0037 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_038) (nb053_alpha_dummy_039 x y) (nb053_wpp_notmem_0078) (nb053_wpp_notmem_0079 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_036) (nb053_alpha_dummy_037 x y) (nb053_wpp_notmem_0080) (nb053_wpp_notmem_0081 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_005) (nb053_alpha_dummy_007 x y) (nb053_wpp_notmem_0038) (nb053_wpp_notmem_0039 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_004) (nb053_alpha_dummy_006 x y) (nb053_wpp_notmem_0040) (nb053_wpp_notmem_0041 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_034) (nb053_alpha_dummy_035 x y) (nb053_wpp_notmem_0082) (nb053_wpp_notmem_0083 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_008) (nb053_alpha_dummy_009 x y) (nb053_wpp_notmem_0044) (nb053_wpp_notmem_0045 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_001) y (nb053_wpp_notmem_0046) (nb053_wpp_notmem_0047 y) (TEnvFresh.consFresh (nb053_alpha_dummy_000) x (nb053_wpp_notmem_0048) (nb053_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb053_alpha_dummy_002) (nb053_alpha_dummy_003 x y) (nb053_wpp_notmem_0050) (nb053_wpp_notmem_0051 x y) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))

noncomputable def nb053_wpp_refl_0004 (x : Var) (y : Var) : TReflOn [((nb053_alpha_dummy_020), (nb053_alpha_dummy_023 x y)), ((nb053_alpha_dummy_019), (nb053_alpha_dummy_022 x y)), ((nb053_alpha_dummy_018), (nb053_alpha_dummy_021 x y)), ((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)), ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)), ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)), ((nb053_alpha_dummy_038), (nb053_alpha_dummy_039 x y)), ((nb053_alpha_dummy_036), (nb053_alpha_dummy_037 x y)), ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)), ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)), ((nb053_alpha_dummy_034), (nb053_alpha_dummy_035 x y)), ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)), ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb053_compact_envfresh_0004 x y)

noncomputable def nb053_split_alpha_0002 (x : Var) (y : Var) : TAlphaWff [((nb053_alpha_dummy_020), (nb053_alpha_dummy_023 x y)), ((nb053_alpha_dummy_019), (nb053_alpha_dummy_022 x y)), ((nb053_alpha_dummy_018), (nb053_alpha_dummy_021 x y)), ((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)), ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)), ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)), ((nb053_alpha_dummy_038), (nb053_alpha_dummy_039 x y)), ((nb053_alpha_dummy_036), (nb053_alpha_dummy_037 x y)), ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)), ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)), ((nb053_alpha_dummy_034), (nb053_alpha_dummy_035 x y)), ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)), ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb053_alpha_dummy_019)) (Class.cv (nb053_alpha_dummy_020))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb053_alpha_dummy_018)) (syn_cun (Class.cv (nb053_alpha_dummy_019)) (Class.cv (nb053_alpha_dummy_020)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb053_alpha_dummy_022 x y)) (Class.cv (nb053_alpha_dummy_023 x y))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb053_alpha_dummy_021 x y)) (syn_cun (Class.cv (nb053_alpha_dummy_022 x y)) (Class.cv (nb053_alpha_dummy_023 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0019 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0017 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0023 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0021 x y) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0019 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0017 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0023 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0021 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb053_alpha_dummy_020), (nb053_alpha_dummy_023 x y)), ((nb053_alpha_dummy_019), (nb053_alpha_dummy_022 x y)), ((nb053_alpha_dummy_018), (nb053_alpha_dummy_021 x y)), ((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)), ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)), ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)), ((nb053_alpha_dummy_038), (nb053_alpha_dummy_039 x y)), ((nb053_alpha_dummy_036), (nb053_alpha_dummy_037 x y)), ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)), ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)), ((nb053_alpha_dummy_034), (nb053_alpha_dummy_035 x y)), ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)), ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))] (syn_c0) (nb053_wpp_refl_0004 x y))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0027 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0025 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0027 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0025 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0031 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0029 x y) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0031 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0029 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb053_wpp_notmem_0084 : (nb053_alpha_dummy_038) ∉ ((syn_cnnc)).fv := by
  simpa only [nb053_alpha_dummy_038, fv_syn_cnnc] using (nb053_compact_fv_empty_0026)

theorem nb053_wpp_notmem_0085 (x : Var) (y : Var) : (nb053_alpha_dummy_039 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb053_alpha_dummy_039, fv_syn_cnnc] using (nb053_compact_fv_empty_0027 x y)

theorem nb053_wpp_notmem_0086 : (nb053_alpha_dummy_036) ∉ ((syn_cnnc)).fv := by
  simpa only [nb053_alpha_dummy_036, fv_syn_cnnc] using (nb053_compact_fv_empty_0028)

theorem nb053_wpp_notmem_0087 (x : Var) (y : Var) : (nb053_alpha_dummy_037 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb053_alpha_dummy_037, fv_syn_cnnc] using (nb053_compact_fv_empty_0029 x y)

theorem nb053_wpp_notmem_0088 : (nb053_alpha_dummy_034) ∉ ((syn_cnnc)).fv := by
  simpa only [nb053_alpha_dummy_034, fv_syn_cnnc] using (nb053_compact_fv_empty_0030)

theorem nb053_wpp_notmem_0089 (x : Var) (y : Var) : (nb053_alpha_dummy_035 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb053_alpha_dummy_035, fv_syn_cnnc] using (nb053_compact_fv_empty_0031 x y)

theorem nb053_compact_envfresh_0005 (x : Var) (y : Var) : TEnvFresh [((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)), ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)), ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)), ((nb053_alpha_dummy_038), (nb053_alpha_dummy_039 x y)), ((nb053_alpha_dummy_036), (nb053_alpha_dummy_037 x y)), ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)), ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)), ((nb053_alpha_dummy_034), (nb053_alpha_dummy_035 x y)), ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)), ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb053_alpha_dummy_016) (nb053_alpha_dummy_017 x y) (nb053_wpp_notmem_0052) (nb053_wpp_notmem_0053 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_012) (nb053_alpha_dummy_014 x y) (nb053_wpp_notmem_0054) (nb053_wpp_notmem_0055 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_013) (nb053_alpha_dummy_015 x y) (nb053_wpp_notmem_0056) (nb053_wpp_notmem_0057 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_038) (nb053_alpha_dummy_039 x y) (nb053_wpp_notmem_0084) (nb053_wpp_notmem_0085 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_036) (nb053_alpha_dummy_037 x y) (nb053_wpp_notmem_0086) (nb053_wpp_notmem_0087 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_005) (nb053_alpha_dummy_007 x y) (nb053_wpp_notmem_0058) (nb053_wpp_notmem_0059 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_004) (nb053_alpha_dummy_006 x y) (nb053_wpp_notmem_0060) (nb053_wpp_notmem_0061 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_034) (nb053_alpha_dummy_035 x y) (nb053_wpp_notmem_0088) (nb053_wpp_notmem_0089 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_008) (nb053_alpha_dummy_009 x y) (nb053_wpp_notmem_0064) (nb053_wpp_notmem_0065 x y) (TEnvFresh.consFresh (nb053_alpha_dummy_001) y (nb053_wpp_notmem_0066) (nb053_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb053_alpha_dummy_000) x (nb053_wpp_notmem_0068) (nb053_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb053_alpha_dummy_002) (nb053_alpha_dummy_003 x y) (nb053_wpp_notmem_0070) (nb053_wpp_notmem_0071 x y) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))

noncomputable def nb053_wpp_refl_0005 (x : Var) (y : Var) : TReflOn [((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)), ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)), ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)), ((nb053_alpha_dummy_038), (nb053_alpha_dummy_039 x y)), ((nb053_alpha_dummy_036), (nb053_alpha_dummy_037 x y)), ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)), ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)), ((nb053_alpha_dummy_034), (nb053_alpha_dummy_035 x y)), ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)), ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb053_compact_envfresh_0005 x y)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
