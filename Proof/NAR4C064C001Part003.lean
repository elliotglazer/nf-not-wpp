import NAR4C064C001Part002

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

theorem nb064_compact_fv_empty_0008 : (nb064_alpha_dummy_015) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0008 : (nb064_alpha_dummy_015) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_015, fv_syn_c1c] using (nb064_compact_fv_empty_0008)

theorem nb064_compact_fv_empty_0009 (r : Var) (a : Var) : (nb064_alpha_dummy_017 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0009 (r : Var) (a : Var) : (nb064_alpha_dummy_017 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_017, fv_syn_c1c] using (nb064_compact_fv_empty_0009 r a)

theorem nb064_compact_fv_empty_0010 : (nb064_alpha_dummy_016) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0010 : (nb064_alpha_dummy_016) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_016, fv_syn_c1c] using (nb064_compact_fv_empty_0010)

theorem nb064_compact_fv_empty_0011 (r : Var) (a : Var) : (nb064_alpha_dummy_018 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0011 (r : Var) (a : Var) : (nb064_alpha_dummy_018 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_018, fv_syn_c1c] using (nb064_compact_fv_empty_0011 r a)

theorem nb064_compact_fv_empty_0012 : (nb064_alpha_dummy_008) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0012 : (nb064_alpha_dummy_008) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_008, fv_syn_c1c] using (nb064_compact_fv_empty_0012)

theorem nb064_compact_fv_empty_0013 (r : Var) (a : Var) : (nb064_alpha_dummy_010 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0013 (r : Var) (a : Var) : (nb064_alpha_dummy_010 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_010, fv_syn_c1c] using (nb064_compact_fv_empty_0013 r a)

theorem nb064_compact_fv_empty_0014 : (nb064_alpha_dummy_007) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0014 : (nb064_alpha_dummy_007) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_007, fv_syn_c1c] using (nb064_compact_fv_empty_0014)

theorem nb064_compact_fv_empty_0015 (r : Var) (a : Var) : (nb064_alpha_dummy_009 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0015 (r : Var) (a : Var) : (nb064_alpha_dummy_009 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_009, fv_syn_c1c] using (nb064_compact_fv_empty_0015 r a)

theorem nb064_compact_fv_empty_0016 : (nb064_alpha_dummy_013) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0016 : (nb064_alpha_dummy_013) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_013, fv_syn_c1c] using (nb064_compact_fv_empty_0016)

theorem nb064_compact_fv_empty_0017 (r : Var) (a : Var) : (nb064_alpha_dummy_014 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0017 (r : Var) (a : Var) : (nb064_alpha_dummy_014 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_014, fv_syn_c1c] using (nb064_compact_fv_empty_0017 r a)

theorem nb064_compact_fv_empty_0018 : (nb064_alpha_dummy_011) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0018 : (nb064_alpha_dummy_011) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_011, fv_syn_c1c] using (nb064_compact_fv_empty_0018)

theorem nb064_compact_fv_empty_0019 (r : Var) (a : Var) : (nb064_alpha_dummy_012 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0019 (r : Var) (a : Var) : (nb064_alpha_dummy_012 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_012, fv_syn_c1c] using (nb064_compact_fv_empty_0019 r a)

theorem nb064_compact_fv_empty_0020 : (nb064_alpha_dummy_000) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0020 : (nb064_alpha_dummy_000) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_000, fv_syn_c1c] using (nb064_compact_fv_empty_0020)

theorem nb064_compact_fv_empty_0021 (a : Var) : a ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0021 (a : Var) : a ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb064_compact_fv_empty_0021 a)

theorem nb064_compact_fv_empty_0022 : (nb064_alpha_dummy_001) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0022 : (nb064_alpha_dummy_001) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_001, fv_syn_c1c] using (nb064_compact_fv_empty_0022)

theorem nb064_compact_fv_empty_0023 (r : Var) : r ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0023 (r : Var) : r ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb064_compact_fv_empty_0023 r)

theorem nb064_compact_fv_empty_0024 : (nb064_alpha_dummy_005) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0024 : (nb064_alpha_dummy_005) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_005, fv_syn_c1c] using (nb064_compact_fv_empty_0024)

theorem nb064_compact_fv_empty_0025 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : (nb064_alpha_dummy_006 x y z r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0025 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : (nb064_alpha_dummy_006 x y z r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_006, fv_syn_c1c] using (nb064_compact_fv_empty_0025 x y z r a)

theorem nb064_compact_envfresh_0000 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb064_alpha_dummy_023), (nb064_alpha_dummy_026 r a)), ((nb064_alpha_dummy_022), (nb064_alpha_dummy_025 r a)), ((nb064_alpha_dummy_021), (nb064_alpha_dummy_024 r a)), ((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_013), (nb064_alpha_dummy_014 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb064_alpha_dummy_023) (nb064_alpha_dummy_026 r a) (nb064_wpp_notmem_0000) (nb064_wpp_notmem_0001 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_022) (nb064_alpha_dummy_025 r a) (nb064_wpp_notmem_0002) (nb064_wpp_notmem_0003 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_021) (nb064_alpha_dummy_024 r a) (nb064_wpp_notmem_0004) (nb064_wpp_notmem_0005 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_019) (nb064_alpha_dummy_020 r a) (nb064_wpp_notmem_0006) (nb064_wpp_notmem_0007 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_015) (nb064_alpha_dummy_017 r a) (nb064_wpp_notmem_0008) (nb064_wpp_notmem_0009 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_016) (nb064_alpha_dummy_018 r a) (nb064_wpp_notmem_0010) (nb064_wpp_notmem_0011 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_008) (nb064_alpha_dummy_010 r a) (nb064_wpp_notmem_0012) (nb064_wpp_notmem_0013 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_007) (nb064_alpha_dummy_009 r a) (nb064_wpp_notmem_0014) (nb064_wpp_notmem_0015 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_013) (nb064_alpha_dummy_014 r a) (nb064_wpp_notmem_0016) (nb064_wpp_notmem_0017 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_011) (nb064_alpha_dummy_012 r a) (nb064_wpp_notmem_0018) (nb064_wpp_notmem_0019 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_000) a (nb064_wpp_notmem_0020) (nb064_wpp_notmem_0021 a) (TEnvFresh.consFresh (nb064_alpha_dummy_001) r (nb064_wpp_notmem_0022) (nb064_wpp_notmem_0023 r) (TEnvFresh.consFresh (nb064_alpha_dummy_005) (nb064_alpha_dummy_006 x y z r a) (nb064_wpp_notmem_0024) (nb064_wpp_notmem_0025 x y z r a) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))

noncomputable def nb064_wpp_refl_0000 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb064_alpha_dummy_023), (nb064_alpha_dummy_026 r a)), ((nb064_alpha_dummy_022), (nb064_alpha_dummy_025 r a)), ((nb064_alpha_dummy_021), (nb064_alpha_dummy_024 r a)), ((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_013), (nb064_alpha_dummy_014 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb064_compact_envfresh_0000 x y z r a)

theorem nb064_wpp_notmem_0026 : (nb064_alpha_dummy_023) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_023, fv_syn_c0] using (nb064_compact_fv_empty_0000)

theorem nb064_wpp_notmem_0027 (r : Var) (a : Var) : (nb064_alpha_dummy_026 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_026, fv_syn_c0] using (nb064_compact_fv_empty_0001 r a)

theorem nb064_wpp_notmem_0028 : (nb064_alpha_dummy_022) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_022, fv_syn_c0] using (nb064_compact_fv_empty_0002)

theorem nb064_wpp_notmem_0029 (r : Var) (a : Var) : (nb064_alpha_dummy_025 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_025, fv_syn_c0] using (nb064_compact_fv_empty_0003 r a)

theorem nb064_wpp_notmem_0030 : (nb064_alpha_dummy_021) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_021, fv_syn_c0] using (nb064_compact_fv_empty_0004)

theorem nb064_wpp_notmem_0031 (r : Var) (a : Var) : (nb064_alpha_dummy_024 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_024, fv_syn_c0] using (nb064_compact_fv_empty_0005 r a)

theorem nb064_wpp_notmem_0032 : (nb064_alpha_dummy_019) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_019, fv_syn_c0] using (nb064_compact_fv_empty_0006)

theorem nb064_wpp_notmem_0033 (r : Var) (a : Var) : (nb064_alpha_dummy_020 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_020, fv_syn_c0] using (nb064_compact_fv_empty_0007 r a)

theorem nb064_wpp_notmem_0034 : (nb064_alpha_dummy_015) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_015, fv_syn_c0] using (nb064_compact_fv_empty_0008)

theorem nb064_wpp_notmem_0035 (r : Var) (a : Var) : (nb064_alpha_dummy_017 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_017, fv_syn_c0] using (nb064_compact_fv_empty_0009 r a)

theorem nb064_wpp_notmem_0036 : (nb064_alpha_dummy_016) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_016, fv_syn_c0] using (nb064_compact_fv_empty_0010)

theorem nb064_wpp_notmem_0037 (r : Var) (a : Var) : (nb064_alpha_dummy_018 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_018, fv_syn_c0] using (nb064_compact_fv_empty_0011 r a)

theorem nb064_wpp_notmem_0038 : (nb064_alpha_dummy_008) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_008, fv_syn_c0] using (nb064_compact_fv_empty_0012)

theorem nb064_wpp_notmem_0039 (r : Var) (a : Var) : (nb064_alpha_dummy_010 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_010, fv_syn_c0] using (nb064_compact_fv_empty_0013 r a)

theorem nb064_wpp_notmem_0040 : (nb064_alpha_dummy_007) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_007, fv_syn_c0] using (nb064_compact_fv_empty_0014)

theorem nb064_wpp_notmem_0041 (r : Var) (a : Var) : (nb064_alpha_dummy_009 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_009, fv_syn_c0] using (nb064_compact_fv_empty_0015 r a)

theorem nb064_wpp_notmem_0042 : (nb064_alpha_dummy_013) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_013, fv_syn_c0] using (nb064_compact_fv_empty_0016)

theorem nb064_wpp_notmem_0043 (r : Var) (a : Var) : (nb064_alpha_dummy_014 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_014, fv_syn_c0] using (nb064_compact_fv_empty_0017 r a)

theorem nb064_wpp_notmem_0044 : (nb064_alpha_dummy_011) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_011, fv_syn_c0] using (nb064_compact_fv_empty_0018)

theorem nb064_wpp_notmem_0045 (r : Var) (a : Var) : (nb064_alpha_dummy_012 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_012, fv_syn_c0] using (nb064_compact_fv_empty_0019 r a)

theorem nb064_wpp_notmem_0046 : (nb064_alpha_dummy_000) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_000, fv_syn_c0] using (nb064_compact_fv_empty_0020)

theorem nb064_wpp_notmem_0047 (a : Var) : a ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb064_compact_fv_empty_0021 a)

theorem nb064_wpp_notmem_0048 : (nb064_alpha_dummy_001) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_001, fv_syn_c0] using (nb064_compact_fv_empty_0022)

theorem nb064_wpp_notmem_0049 (r : Var) : r ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb064_compact_fv_empty_0023 r)

theorem nb064_wpp_notmem_0050 : (nb064_alpha_dummy_005) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_005, fv_syn_c0] using (nb064_compact_fv_empty_0024)

theorem nb064_wpp_notmem_0051 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : (nb064_alpha_dummy_006 x y z r a) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_006, fv_syn_c0] using (nb064_compact_fv_empty_0025 x y z r a)

theorem nb064_compact_envfresh_0001 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb064_alpha_dummy_023), (nb064_alpha_dummy_026 r a)), ((nb064_alpha_dummy_022), (nb064_alpha_dummy_025 r a)), ((nb064_alpha_dummy_021), (nb064_alpha_dummy_024 r a)), ((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_013), (nb064_alpha_dummy_014 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb064_alpha_dummy_023) (nb064_alpha_dummy_026 r a) (nb064_wpp_notmem_0026) (nb064_wpp_notmem_0027 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_022) (nb064_alpha_dummy_025 r a) (nb064_wpp_notmem_0028) (nb064_wpp_notmem_0029 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_021) (nb064_alpha_dummy_024 r a) (nb064_wpp_notmem_0030) (nb064_wpp_notmem_0031 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_019) (nb064_alpha_dummy_020 r a) (nb064_wpp_notmem_0032) (nb064_wpp_notmem_0033 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_015) (nb064_alpha_dummy_017 r a) (nb064_wpp_notmem_0034) (nb064_wpp_notmem_0035 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_016) (nb064_alpha_dummy_018 r a) (nb064_wpp_notmem_0036) (nb064_wpp_notmem_0037 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_008) (nb064_alpha_dummy_010 r a) (nb064_wpp_notmem_0038) (nb064_wpp_notmem_0039 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_007) (nb064_alpha_dummy_009 r a) (nb064_wpp_notmem_0040) (nb064_wpp_notmem_0041 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_013) (nb064_alpha_dummy_014 r a) (nb064_wpp_notmem_0042) (nb064_wpp_notmem_0043 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_011) (nb064_alpha_dummy_012 r a) (nb064_wpp_notmem_0044) (nb064_wpp_notmem_0045 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_000) a (nb064_wpp_notmem_0046) (nb064_wpp_notmem_0047 a) (TEnvFresh.consFresh (nb064_alpha_dummy_001) r (nb064_wpp_notmem_0048) (nb064_wpp_notmem_0049 r) (TEnvFresh.consFresh (nb064_alpha_dummy_005) (nb064_alpha_dummy_006 x y z r a) (nb064_wpp_notmem_0050) (nb064_wpp_notmem_0051 x y z r a) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))

noncomputable def nb064_wpp_refl_0001 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb064_alpha_dummy_023), (nb064_alpha_dummy_026 r a)), ((nb064_alpha_dummy_022), (nb064_alpha_dummy_025 r a)), ((nb064_alpha_dummy_021), (nb064_alpha_dummy_024 r a)), ((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_013), (nb064_alpha_dummy_014 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb064_compact_envfresh_0001 x y z r a)

noncomputable def nb064_split_alpha_0000 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TAlphaWff [((nb064_alpha_dummy_023), (nb064_alpha_dummy_026 r a)), ((nb064_alpha_dummy_022), (nb064_alpha_dummy_025 r a)), ((nb064_alpha_dummy_021), (nb064_alpha_dummy_024 r a)), ((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_013), (nb064_alpha_dummy_014 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb064_alpha_dummy_022)) (Class.cv (nb064_alpha_dummy_023))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb064_alpha_dummy_021)) (syn_cun (Class.cv (nb064_alpha_dummy_022)) (Class.cv (nb064_alpha_dummy_023)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb064_alpha_dummy_025 r a)) (Class.cv (nb064_alpha_dummy_026 r a))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb064_alpha_dummy_024 r a)) (syn_cun (Class.cv (nb064_alpha_dummy_025 r a)) (Class.cv (nb064_alpha_dummy_026 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0019 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0017 r a) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0023 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0021 r a) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0019 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0017 r a) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0023 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0021 r a) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb064_alpha_dummy_023), (nb064_alpha_dummy_026 r a)), ((nb064_alpha_dummy_022), (nb064_alpha_dummy_025 r a)), ((nb064_alpha_dummy_021), (nb064_alpha_dummy_024 r a)), ((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_013), (nb064_alpha_dummy_014 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] (syn_c0) (nb064_wpp_refl_0001 x y z r a))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0027 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0025 r a) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0027 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0025 r a) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0031 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0029 r a) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0031 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0029 r a) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb064_wpp_notmem_0052 : (nb064_alpha_dummy_019) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_019, fv_syn_cnnc] using (nb064_compact_fv_empty_0006)

theorem nb064_wpp_notmem_0053 (r : Var) (a : Var) : (nb064_alpha_dummy_020 r a) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_020, fv_syn_cnnc] using (nb064_compact_fv_empty_0007 r a)

theorem nb064_wpp_notmem_0054 : (nb064_alpha_dummy_015) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_015, fv_syn_cnnc] using (nb064_compact_fv_empty_0008)

theorem nb064_wpp_notmem_0055 (r : Var) (a : Var) : (nb064_alpha_dummy_017 r a) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_017, fv_syn_cnnc] using (nb064_compact_fv_empty_0009 r a)

theorem nb064_wpp_notmem_0056 : (nb064_alpha_dummy_016) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_016, fv_syn_cnnc] using (nb064_compact_fv_empty_0010)

theorem nb064_wpp_notmem_0057 (r : Var) (a : Var) : (nb064_alpha_dummy_018 r a) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_018, fv_syn_cnnc] using (nb064_compact_fv_empty_0011 r a)

theorem nb064_wpp_notmem_0058 : (nb064_alpha_dummy_008) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_008, fv_syn_cnnc] using (nb064_compact_fv_empty_0012)

theorem nb064_wpp_notmem_0059 (r : Var) (a : Var) : (nb064_alpha_dummy_010 r a) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_010, fv_syn_cnnc] using (nb064_compact_fv_empty_0013 r a)

theorem nb064_wpp_notmem_0060 : (nb064_alpha_dummy_007) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_007, fv_syn_cnnc] using (nb064_compact_fv_empty_0014)

theorem nb064_wpp_notmem_0061 (r : Var) (a : Var) : (nb064_alpha_dummy_009 r a) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_009, fv_syn_cnnc] using (nb064_compact_fv_empty_0015 r a)

theorem nb064_wpp_notmem_0062 : (nb064_alpha_dummy_013) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_013, fv_syn_cnnc] using (nb064_compact_fv_empty_0016)

theorem nb064_wpp_notmem_0063 (r : Var) (a : Var) : (nb064_alpha_dummy_014 r a) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_014, fv_syn_cnnc] using (nb064_compact_fv_empty_0017 r a)

theorem nb064_wpp_notmem_0064 : (nb064_alpha_dummy_011) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_011, fv_syn_cnnc] using (nb064_compact_fv_empty_0018)

theorem nb064_wpp_notmem_0065 (r : Var) (a : Var) : (nb064_alpha_dummy_012 r a) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_012, fv_syn_cnnc] using (nb064_compact_fv_empty_0019 r a)

theorem nb064_wpp_notmem_0066 : (nb064_alpha_dummy_000) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_000, fv_syn_cnnc] using (nb064_compact_fv_empty_0020)

theorem nb064_wpp_notmem_0067 (a : Var) : a ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb064_compact_fv_empty_0021 a)

theorem nb064_wpp_notmem_0068 : (nb064_alpha_dummy_001) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_001, fv_syn_cnnc] using (nb064_compact_fv_empty_0022)

theorem nb064_wpp_notmem_0069 (r : Var) : r ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb064_compact_fv_empty_0023 r)

theorem nb064_wpp_notmem_0070 : (nb064_alpha_dummy_005) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_005, fv_syn_cnnc] using (nb064_compact_fv_empty_0024)

theorem nb064_wpp_notmem_0071 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : (nb064_alpha_dummy_006 x y z r a) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_006, fv_syn_cnnc] using (nb064_compact_fv_empty_0025 x y z r a)

theorem nb064_compact_envfresh_0002 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_013), (nb064_alpha_dummy_014 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb064_alpha_dummy_019) (nb064_alpha_dummy_020 r a) (nb064_wpp_notmem_0052) (nb064_wpp_notmem_0053 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_015) (nb064_alpha_dummy_017 r a) (nb064_wpp_notmem_0054) (nb064_wpp_notmem_0055 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_016) (nb064_alpha_dummy_018 r a) (nb064_wpp_notmem_0056) (nb064_wpp_notmem_0057 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_008) (nb064_alpha_dummy_010 r a) (nb064_wpp_notmem_0058) (nb064_wpp_notmem_0059 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_007) (nb064_alpha_dummy_009 r a) (nb064_wpp_notmem_0060) (nb064_wpp_notmem_0061 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_013) (nb064_alpha_dummy_014 r a) (nb064_wpp_notmem_0062) (nb064_wpp_notmem_0063 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_011) (nb064_alpha_dummy_012 r a) (nb064_wpp_notmem_0064) (nb064_wpp_notmem_0065 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_000) a (nb064_wpp_notmem_0066) (nb064_wpp_notmem_0067 a) (TEnvFresh.consFresh (nb064_alpha_dummy_001) r (nb064_wpp_notmem_0068) (nb064_wpp_notmem_0069 r) (TEnvFresh.consFresh (nb064_alpha_dummy_005) (nb064_alpha_dummy_006 x y z r a) (nb064_wpp_notmem_0070) (nb064_wpp_notmem_0071 x y z r a) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))

noncomputable def nb064_wpp_refl_0002 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_013), (nb064_alpha_dummy_014 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb064_compact_envfresh_0002 x y z r a)

noncomputable def nb064_split_alpha_0001 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) (dv_a_r : a ≠ r) : TAlphaWff [((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_013), (nb064_alpha_dummy_014 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] (Wff.imp (Wff.classMem (Class.cv (nb064_alpha_dummy_008)) (Class.cv (nb064_alpha_dummy_001))) (Wff.neg (Wff.classEq (Class.cv (nb064_alpha_dummy_007)) (syn_cphi (Class.cv (nb064_alpha_dummy_008)))))) (Wff.imp (Wff.classMem (Class.cv (nb064_alpha_dummy_010 r a)) (Class.cv r)) (Wff.neg (Wff.classEq (Class.cv (nb064_alpha_dummy_009 r a)) (syn_cphi (Class.cv (nb064_alpha_dummy_010 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0004) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0006 r a) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0004) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0006 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0008) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0009 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0005) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0007 r a) 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) (Ne.symm dv_a_r) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_001))).fv ∪ ((Class.cv (nb064_alpha_dummy_000))).fv) (by decide)) (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0010) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0011 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0010) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0011 r a) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_008))).fv) (by decide)) (freshVar_injective (((Class.cv (nb064_alpha_dummy_010 r a))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0014) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0015 r a) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0015 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb064_alpha_dummy_023), (nb064_alpha_dummy_026 r a)), ((nb064_alpha_dummy_022), (nb064_alpha_dummy_025 r a)), ((nb064_alpha_dummy_021), (nb064_alpha_dummy_024 r a)), ((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_013), (nb064_alpha_dummy_014 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] (syn_c1c) (nb064_wpp_refl_0000 x y z r a))) (TAlphaWff.neg (TAlphaWff.neg (nb064_split_alpha_0000 x y z r a)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_013), (nb064_alpha_dummy_014 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] (syn_cnnc) (nb064_wpp_refl_0002 x y z r a))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_013), (nb064_alpha_dummy_014 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] (syn_cnnc) (nb064_wpp_refl_0002 x y z r a))))))))))))))))))))

theorem nb064_compact_fv_empty_0026 : (nb064_alpha_dummy_041) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0072 : (nb064_alpha_dummy_041) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_041, fv_syn_c1c] using (nb064_compact_fv_empty_0026)

theorem nb064_compact_fv_empty_0027 (r : Var) (a : Var) : (nb064_alpha_dummy_042 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0073 (r : Var) (a : Var) : (nb064_alpha_dummy_042 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_042, fv_syn_c1c] using (nb064_compact_fv_empty_0027 r a)

theorem nb064_compact_fv_empty_0028 : (nb064_alpha_dummy_039) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0074 : (nb064_alpha_dummy_039) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_039, fv_syn_c1c] using (nb064_compact_fv_empty_0028)

theorem nb064_compact_fv_empty_0029 (r : Var) (a : Var) : (nb064_alpha_dummy_040 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0075 (r : Var) (a : Var) : (nb064_alpha_dummy_040 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_040, fv_syn_c1c] using (nb064_compact_fv_empty_0029 r a)

theorem nb064_compact_fv_empty_0030 : (nb064_alpha_dummy_037) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0076 : (nb064_alpha_dummy_037) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_037, fv_syn_c1c] using (nb064_compact_fv_empty_0030)

theorem nb064_compact_fv_empty_0031 (r : Var) (a : Var) : (nb064_alpha_dummy_038 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0077 (r : Var) (a : Var) : (nb064_alpha_dummy_038 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_038, fv_syn_c1c] using (nb064_compact_fv_empty_0031 r a)

theorem nb064_compact_envfresh_0003 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb064_alpha_dummy_023), (nb064_alpha_dummy_026 r a)), ((nb064_alpha_dummy_022), (nb064_alpha_dummy_025 r a)), ((nb064_alpha_dummy_021), (nb064_alpha_dummy_024 r a)), ((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_041), (nb064_alpha_dummy_042 r a)), ((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb064_alpha_dummy_023) (nb064_alpha_dummy_026 r a) (nb064_wpp_notmem_0000) (nb064_wpp_notmem_0001 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_022) (nb064_alpha_dummy_025 r a) (nb064_wpp_notmem_0002) (nb064_wpp_notmem_0003 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_021) (nb064_alpha_dummy_024 r a) (nb064_wpp_notmem_0004) (nb064_wpp_notmem_0005 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_019) (nb064_alpha_dummy_020 r a) (nb064_wpp_notmem_0006) (nb064_wpp_notmem_0007 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_015) (nb064_alpha_dummy_017 r a) (nb064_wpp_notmem_0008) (nb064_wpp_notmem_0009 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_016) (nb064_alpha_dummy_018 r a) (nb064_wpp_notmem_0010) (nb064_wpp_notmem_0011 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_041) (nb064_alpha_dummy_042 r a) (nb064_wpp_notmem_0072) (nb064_wpp_notmem_0073 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_039) (nb064_alpha_dummy_040 r a) (nb064_wpp_notmem_0074) (nb064_wpp_notmem_0075 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_008) (nb064_alpha_dummy_010 r a) (nb064_wpp_notmem_0012) (nb064_wpp_notmem_0013 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_007) (nb064_alpha_dummy_009 r a) (nb064_wpp_notmem_0014) (nb064_wpp_notmem_0015 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_037) (nb064_alpha_dummy_038 r a) (nb064_wpp_notmem_0076) (nb064_wpp_notmem_0077 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_011) (nb064_alpha_dummy_012 r a) (nb064_wpp_notmem_0018) (nb064_wpp_notmem_0019 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_000) a (nb064_wpp_notmem_0020) (nb064_wpp_notmem_0021 a) (TEnvFresh.consFresh (nb064_alpha_dummy_001) r (nb064_wpp_notmem_0022) (nb064_wpp_notmem_0023 r) (TEnvFresh.consFresh (nb064_alpha_dummy_005) (nb064_alpha_dummy_006 x y z r a) (nb064_wpp_notmem_0024) (nb064_wpp_notmem_0025 x y z r a) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb064_wpp_refl_0003 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb064_alpha_dummy_023), (nb064_alpha_dummy_026 r a)), ((nb064_alpha_dummy_022), (nb064_alpha_dummy_025 r a)), ((nb064_alpha_dummy_021), (nb064_alpha_dummy_024 r a)), ((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_041), (nb064_alpha_dummy_042 r a)), ((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb064_compact_envfresh_0003 x y z r a)

theorem nb064_wpp_notmem_0078 : (nb064_alpha_dummy_041) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_041, fv_syn_c0] using (nb064_compact_fv_empty_0026)

theorem nb064_wpp_notmem_0079 (r : Var) (a : Var) : (nb064_alpha_dummy_042 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_042, fv_syn_c0] using (nb064_compact_fv_empty_0027 r a)

theorem nb064_wpp_notmem_0080 : (nb064_alpha_dummy_039) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_039, fv_syn_c0] using (nb064_compact_fv_empty_0028)

theorem nb064_wpp_notmem_0081 (r : Var) (a : Var) : (nb064_alpha_dummy_040 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_040, fv_syn_c0] using (nb064_compact_fv_empty_0029 r a)

theorem nb064_wpp_notmem_0082 : (nb064_alpha_dummy_037) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_037, fv_syn_c0] using (nb064_compact_fv_empty_0030)

theorem nb064_wpp_notmem_0083 (r : Var) (a : Var) : (nb064_alpha_dummy_038 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_038, fv_syn_c0] using (nb064_compact_fv_empty_0031 r a)

theorem nb064_compact_envfresh_0004 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb064_alpha_dummy_023), (nb064_alpha_dummy_026 r a)), ((nb064_alpha_dummy_022), (nb064_alpha_dummy_025 r a)), ((nb064_alpha_dummy_021), (nb064_alpha_dummy_024 r a)), ((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_041), (nb064_alpha_dummy_042 r a)), ((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb064_alpha_dummy_023) (nb064_alpha_dummy_026 r a) (nb064_wpp_notmem_0026) (nb064_wpp_notmem_0027 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_022) (nb064_alpha_dummy_025 r a) (nb064_wpp_notmem_0028) (nb064_wpp_notmem_0029 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_021) (nb064_alpha_dummy_024 r a) (nb064_wpp_notmem_0030) (nb064_wpp_notmem_0031 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_019) (nb064_alpha_dummy_020 r a) (nb064_wpp_notmem_0032) (nb064_wpp_notmem_0033 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_015) (nb064_alpha_dummy_017 r a) (nb064_wpp_notmem_0034) (nb064_wpp_notmem_0035 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_016) (nb064_alpha_dummy_018 r a) (nb064_wpp_notmem_0036) (nb064_wpp_notmem_0037 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_041) (nb064_alpha_dummy_042 r a) (nb064_wpp_notmem_0078) (nb064_wpp_notmem_0079 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_039) (nb064_alpha_dummy_040 r a) (nb064_wpp_notmem_0080) (nb064_wpp_notmem_0081 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_008) (nb064_alpha_dummy_010 r a) (nb064_wpp_notmem_0038) (nb064_wpp_notmem_0039 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_007) (nb064_alpha_dummy_009 r a) (nb064_wpp_notmem_0040) (nb064_wpp_notmem_0041 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_037) (nb064_alpha_dummy_038 r a) (nb064_wpp_notmem_0082) (nb064_wpp_notmem_0083 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_011) (nb064_alpha_dummy_012 r a) (nb064_wpp_notmem_0044) (nb064_wpp_notmem_0045 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_000) a (nb064_wpp_notmem_0046) (nb064_wpp_notmem_0047 a) (TEnvFresh.consFresh (nb064_alpha_dummy_001) r (nb064_wpp_notmem_0048) (nb064_wpp_notmem_0049 r) (TEnvFresh.consFresh (nb064_alpha_dummy_005) (nb064_alpha_dummy_006 x y z r a) (nb064_wpp_notmem_0050) (nb064_wpp_notmem_0051 x y z r a) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))

noncomputable def nb064_wpp_refl_0004 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb064_alpha_dummy_023), (nb064_alpha_dummy_026 r a)), ((nb064_alpha_dummy_022), (nb064_alpha_dummy_025 r a)), ((nb064_alpha_dummy_021), (nb064_alpha_dummy_024 r a)), ((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_041), (nb064_alpha_dummy_042 r a)), ((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb064_compact_envfresh_0004 x y z r a)

noncomputable def nb064_split_alpha_0002 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TAlphaWff [((nb064_alpha_dummy_023), (nb064_alpha_dummy_026 r a)), ((nb064_alpha_dummy_022), (nb064_alpha_dummy_025 r a)), ((nb064_alpha_dummy_021), (nb064_alpha_dummy_024 r a)), ((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_041), (nb064_alpha_dummy_042 r a)), ((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb064_alpha_dummy_022)) (Class.cv (nb064_alpha_dummy_023))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb064_alpha_dummy_021)) (syn_cun (Class.cv (nb064_alpha_dummy_022)) (Class.cv (nb064_alpha_dummy_023)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb064_alpha_dummy_025 r a)) (Class.cv (nb064_alpha_dummy_026 r a))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb064_alpha_dummy_024 r a)) (syn_cun (Class.cv (nb064_alpha_dummy_025 r a)) (Class.cv (nb064_alpha_dummy_026 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0019 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0017 r a) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0023 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0021 r a) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0019 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0017 r a) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0023 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0021 r a) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb064_alpha_dummy_023), (nb064_alpha_dummy_026 r a)), ((nb064_alpha_dummy_022), (nb064_alpha_dummy_025 r a)), ((nb064_alpha_dummy_021), (nb064_alpha_dummy_024 r a)), ((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_041), (nb064_alpha_dummy_042 r a)), ((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] (syn_c0) (nb064_wpp_refl_0004 x y z r a))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0027 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0025 r a) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0027 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0025 r a) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0031 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0029 r a) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0031 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0029 r a) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb064_wpp_notmem_0084 : (nb064_alpha_dummy_041) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_041, fv_syn_cnnc] using (nb064_compact_fv_empty_0026)

theorem nb064_wpp_notmem_0085 (r : Var) (a : Var) : (nb064_alpha_dummy_042 r a) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_042, fv_syn_cnnc] using (nb064_compact_fv_empty_0027 r a)

theorem nb064_wpp_notmem_0086 : (nb064_alpha_dummy_039) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_039, fv_syn_cnnc] using (nb064_compact_fv_empty_0028)

theorem nb064_wpp_notmem_0087 (r : Var) (a : Var) : (nb064_alpha_dummy_040 r a) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_040, fv_syn_cnnc] using (nb064_compact_fv_empty_0029 r a)

theorem nb064_wpp_notmem_0088 : (nb064_alpha_dummy_037) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_037, fv_syn_cnnc] using (nb064_compact_fv_empty_0030)

theorem nb064_wpp_notmem_0089 (r : Var) (a : Var) : (nb064_alpha_dummy_038 r a) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_038, fv_syn_cnnc] using (nb064_compact_fv_empty_0031 r a)

theorem nb064_compact_envfresh_0005 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_041), (nb064_alpha_dummy_042 r a)), ((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb064_alpha_dummy_019) (nb064_alpha_dummy_020 r a) (nb064_wpp_notmem_0052) (nb064_wpp_notmem_0053 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_015) (nb064_alpha_dummy_017 r a) (nb064_wpp_notmem_0054) (nb064_wpp_notmem_0055 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_016) (nb064_alpha_dummy_018 r a) (nb064_wpp_notmem_0056) (nb064_wpp_notmem_0057 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_041) (nb064_alpha_dummy_042 r a) (nb064_wpp_notmem_0084) (nb064_wpp_notmem_0085 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_039) (nb064_alpha_dummy_040 r a) (nb064_wpp_notmem_0086) (nb064_wpp_notmem_0087 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_008) (nb064_alpha_dummy_010 r a) (nb064_wpp_notmem_0058) (nb064_wpp_notmem_0059 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_007) (nb064_alpha_dummy_009 r a) (nb064_wpp_notmem_0060) (nb064_wpp_notmem_0061 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_037) (nb064_alpha_dummy_038 r a) (nb064_wpp_notmem_0088) (nb064_wpp_notmem_0089 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_011) (nb064_alpha_dummy_012 r a) (nb064_wpp_notmem_0064) (nb064_wpp_notmem_0065 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_000) a (nb064_wpp_notmem_0066) (nb064_wpp_notmem_0067 a) (TEnvFresh.consFresh (nb064_alpha_dummy_001) r (nb064_wpp_notmem_0068) (nb064_wpp_notmem_0069 r) (TEnvFresh.consFresh (nb064_alpha_dummy_005) (nb064_alpha_dummy_006 x y z r a) (nb064_wpp_notmem_0070) (nb064_wpp_notmem_0071 x y z r a) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))

noncomputable def nb064_wpp_refl_0005 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_041), (nb064_alpha_dummy_042 r a)), ((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb064_compact_envfresh_0005 x y z r a)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
