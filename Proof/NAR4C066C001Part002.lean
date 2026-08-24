import NAR4C066C001Part001

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

noncomputable def nb066_wpp_refl_0000 (x : Var) (y : Var) (A : Class) (R : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) : TReflOn [((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)] (A).fv :=
  TEnvFresh.reflOn (nb066_compact_envfresh_0000 x y A R dv_A_x dv_A_y)

theorem nb066_compact_fv_empty_0000 (A : Class) (R : Class) : (nb066_alpha_dummy_024 A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0004 (A : Class) (R : Class) : (nb066_alpha_dummy_024 A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_024, fv_syn_c1c] using (nb066_compact_fv_empty_0000 A R)

theorem nb066_compact_fv_empty_0001 (x : Var) (R : Class) : (nb066_alpha_dummy_027 x R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0005 (x : Var) (R : Class) : (nb066_alpha_dummy_027 x R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_027, fv_syn_c1c] using (nb066_compact_fv_empty_0001 x R)

theorem nb066_compact_fv_empty_0002 (A : Class) (R : Class) : (nb066_alpha_dummy_023 A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0006 (A : Class) (R : Class) : (nb066_alpha_dummy_023 A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_023, fv_syn_c1c] using (nb066_compact_fv_empty_0002 A R)

theorem nb066_compact_fv_empty_0003 (x : Var) (R : Class) : (nb066_alpha_dummy_026 x R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0007 (x : Var) (R : Class) : (nb066_alpha_dummy_026 x R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_026, fv_syn_c1c] using (nb066_compact_fv_empty_0003 x R)

theorem nb066_compact_fv_empty_0004 (A : Class) (R : Class) : (nb066_alpha_dummy_022 A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0008 (A : Class) (R : Class) : (nb066_alpha_dummy_022 A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_022, fv_syn_c1c] using (nb066_compact_fv_empty_0004 A R)

theorem nb066_compact_fv_empty_0005 (x : Var) (R : Class) : (nb066_alpha_dummy_025 x R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0009 (x : Var) (R : Class) : (nb066_alpha_dummy_025 x R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_025, fv_syn_c1c] using (nb066_compact_fv_empty_0005 x R)

theorem nb066_compact_fv_empty_0006 (A : Class) (R : Class) : (nb066_alpha_dummy_020 A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0010 (A : Class) (R : Class) : (nb066_alpha_dummy_020 A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_020, fv_syn_c1c] using (nb066_compact_fv_empty_0006 A R)

theorem nb066_compact_fv_empty_0007 (x : Var) (R : Class) : (nb066_alpha_dummy_021 x R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0011 (x : Var) (R : Class) : (nb066_alpha_dummy_021 x R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_021, fv_syn_c1c] using (nb066_compact_fv_empty_0007 x R)

theorem nb066_compact_fv_empty_0008 (A : Class) (R : Class) : (nb066_alpha_dummy_016 A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0012 (A : Class) (R : Class) : (nb066_alpha_dummy_016 A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_016, fv_syn_c1c] using (nb066_compact_fv_empty_0008 A R)

theorem nb066_compact_fv_empty_0009 (x : Var) (R : Class) : (nb066_alpha_dummy_018 x R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0013 (x : Var) (R : Class) : (nb066_alpha_dummy_018 x R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_018, fv_syn_c1c] using (nb066_compact_fv_empty_0009 x R)

theorem nb066_compact_fv_empty_0010 (A : Class) (R : Class) : (nb066_alpha_dummy_017 A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0014 (A : Class) (R : Class) : (nb066_alpha_dummy_017 A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_017, fv_syn_c1c] using (nb066_compact_fv_empty_0010 A R)

theorem nb066_compact_fv_empty_0011 (x : Var) (R : Class) : (nb066_alpha_dummy_019 x R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0015 (x : Var) (R : Class) : (nb066_alpha_dummy_019 x R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_019, fv_syn_c1c] using (nb066_compact_fv_empty_0011 x R)

theorem nb066_compact_fv_empty_0012 (A : Class) (R : Class) : (nb066_alpha_dummy_009 A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0016 (A : Class) (R : Class) : (nb066_alpha_dummy_009 A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_009, fv_syn_c1c] using (nb066_compact_fv_empty_0012 A R)

theorem nb066_compact_fv_empty_0013 (x : Var) (R : Class) : (nb066_alpha_dummy_011 x R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0017 (x : Var) (R : Class) : (nb066_alpha_dummy_011 x R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_011, fv_syn_c1c] using (nb066_compact_fv_empty_0013 x R)

theorem nb066_compact_fv_empty_0014 (A : Class) (R : Class) : (nb066_alpha_dummy_008 A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0018 (A : Class) (R : Class) : (nb066_alpha_dummy_008 A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_008, fv_syn_c1c] using (nb066_compact_fv_empty_0014 A R)

theorem nb066_compact_fv_empty_0015 (x : Var) (R : Class) : (nb066_alpha_dummy_010 x R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0019 (x : Var) (R : Class) : (nb066_alpha_dummy_010 x R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_010, fv_syn_c1c] using (nb066_compact_fv_empty_0015 x R)

theorem nb066_compact_fv_empty_0016 (A : Class) (R : Class) : (nb066_alpha_dummy_014 A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0020 (A : Class) (R : Class) : (nb066_alpha_dummy_014 A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_014, fv_syn_c1c] using (nb066_compact_fv_empty_0016 A R)

theorem nb066_compact_fv_empty_0017 (x : Var) (R : Class) : (nb066_alpha_dummy_015 x R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0021 (x : Var) (R : Class) : (nb066_alpha_dummy_015 x R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_015, fv_syn_c1c] using (nb066_compact_fv_empty_0017 x R)

theorem nb066_compact_fv_empty_0018 (A : Class) (R : Class) : (nb066_alpha_dummy_012 A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0022 (A : Class) (R : Class) : (nb066_alpha_dummy_012 A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_012, fv_syn_c1c] using (nb066_compact_fv_empty_0018 A R)

theorem nb066_compact_fv_empty_0019 (x : Var) (R : Class) : (nb066_alpha_dummy_013 x R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0023 (x : Var) (R : Class) : (nb066_alpha_dummy_013 x R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_013, fv_syn_c1c] using (nb066_compact_fv_empty_0019 x R)

theorem nb066_compact_fv_empty_0020 (A : Class) (R : Class) : (nb066_alpha_dummy_003 A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0024 (A : Class) (R : Class) : (nb066_alpha_dummy_003 A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_003, fv_syn_c1c] using (nb066_compact_fv_empty_0020 A R)

theorem nb066_compact_fv_empty_0021 (x : Var) (R : Class) : (nb066_alpha_dummy_005 x R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0025 (x : Var) (R : Class) : (nb066_alpha_dummy_005 x R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_005, fv_syn_c1c] using (nb066_compact_fv_empty_0021 x R)

theorem nb066_compact_fv_empty_0022 (A : Class) (R : Class) : (nb066_alpha_dummy_002 A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0026 (A : Class) (R : Class) : (nb066_alpha_dummy_002 A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_002, fv_syn_c1c] using (nb066_compact_fv_empty_0022 A R)

theorem nb066_compact_fv_empty_0023 (x : Var) (R : Class) : (nb066_alpha_dummy_004 x R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0027 (x : Var) (R : Class) : (nb066_alpha_dummy_004 x R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_004, fv_syn_c1c] using (nb066_compact_fv_empty_0023 x R)

theorem nb066_compact_fv_empty_0024 (A : Class) (R : Class) : (nb066_alpha_dummy_000 A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0028 (A : Class) (R : Class) : (nb066_alpha_dummy_000 A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_000, fv_syn_c1c] using (nb066_compact_fv_empty_0024 A R)

theorem nb066_compact_fv_empty_0025 (x : Var) : x ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0029 (x : Var) : x ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb066_compact_fv_empty_0025 x)

theorem nb066_compact_fv_empty_0026 (A : Class) (R : Class) : (nb066_alpha_dummy_001 A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0030 (A : Class) (R : Class) : (nb066_alpha_dummy_001 A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_001, fv_syn_c1c] using (nb066_compact_fv_empty_0026 A R)

theorem nb066_compact_fv_empty_0027 (y : Var) : y ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0031 (y : Var) : y ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb066_compact_fv_empty_0027 y)

theorem nb066_compact_envfresh_0001 (x : Var) (y : Var) (A : Class) (R : Class) : TEnvFresh [((nb066_alpha_dummy_024 A R), (nb066_alpha_dummy_027 x R)), ((nb066_alpha_dummy_023 A R), (nb066_alpha_dummy_026 x R)), ((nb066_alpha_dummy_022 A R), (nb066_alpha_dummy_025 x R)), ((nb066_alpha_dummy_020 A R), (nb066_alpha_dummy_021 x R)), ((nb066_alpha_dummy_016 A R), (nb066_alpha_dummy_018 x R)), ((nb066_alpha_dummy_017 A R), (nb066_alpha_dummy_019 x R)), ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)), ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)), ((nb066_alpha_dummy_014 A R), (nb066_alpha_dummy_015 x R)), ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)), ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)), ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)), ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb066_alpha_dummy_024 A R) (nb066_alpha_dummy_027 x R) (nb066_wpp_notmem_0004 A R) (nb066_wpp_notmem_0005 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_023 A R) (nb066_alpha_dummy_026 x R) (nb066_wpp_notmem_0006 A R) (nb066_wpp_notmem_0007 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_022 A R) (nb066_alpha_dummy_025 x R) (nb066_wpp_notmem_0008 A R) (nb066_wpp_notmem_0009 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_020 A R) (nb066_alpha_dummy_021 x R) (nb066_wpp_notmem_0010 A R) (nb066_wpp_notmem_0011 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_016 A R) (nb066_alpha_dummy_018 x R) (nb066_wpp_notmem_0012 A R) (nb066_wpp_notmem_0013 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_017 A R) (nb066_alpha_dummy_019 x R) (nb066_wpp_notmem_0014 A R) (nb066_wpp_notmem_0015 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_009 A R) (nb066_alpha_dummy_011 x R) (nb066_wpp_notmem_0016 A R) (nb066_wpp_notmem_0017 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_008 A R) (nb066_alpha_dummy_010 x R) (nb066_wpp_notmem_0018 A R) (nb066_wpp_notmem_0019 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_014 A R) (nb066_alpha_dummy_015 x R) (nb066_wpp_notmem_0020 A R) (nb066_wpp_notmem_0021 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_012 A R) (nb066_alpha_dummy_013 x R) (nb066_wpp_notmem_0022 A R) (nb066_wpp_notmem_0023 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_003 A R) (nb066_alpha_dummy_005 x R) (nb066_wpp_notmem_0024 A R) (nb066_wpp_notmem_0025 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_002 A R) (nb066_alpha_dummy_004 x R) (nb066_wpp_notmem_0026 A R) (nb066_wpp_notmem_0027 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_000 A R) x (nb066_wpp_notmem_0028 A R) (nb066_wpp_notmem_0029 x) (TEnvFresh.consFresh (nb066_alpha_dummy_001 A R) y (nb066_wpp_notmem_0030 A R) (nb066_wpp_notmem_0031 y) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))

noncomputable def nb066_wpp_refl_0001 (x : Var) (y : Var) (A : Class) (R : Class) : TReflOn [((nb066_alpha_dummy_024 A R), (nb066_alpha_dummy_027 x R)), ((nb066_alpha_dummy_023 A R), (nb066_alpha_dummy_026 x R)), ((nb066_alpha_dummy_022 A R), (nb066_alpha_dummy_025 x R)), ((nb066_alpha_dummy_020 A R), (nb066_alpha_dummy_021 x R)), ((nb066_alpha_dummy_016 A R), (nb066_alpha_dummy_018 x R)), ((nb066_alpha_dummy_017 A R), (nb066_alpha_dummy_019 x R)), ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)), ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)), ((nb066_alpha_dummy_014 A R), (nb066_alpha_dummy_015 x R)), ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)), ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)), ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)), ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb066_compact_envfresh_0001 x y A R)

theorem nb066_wpp_notmem_0032 (A : Class) (R : Class) : (nb066_alpha_dummy_024 A R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_024, fv_syn_c0] using (nb066_compact_fv_empty_0000 A R)

theorem nb066_wpp_notmem_0033 (x : Var) (R : Class) : (nb066_alpha_dummy_027 x R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_027, fv_syn_c0] using (nb066_compact_fv_empty_0001 x R)

theorem nb066_wpp_notmem_0034 (A : Class) (R : Class) : (nb066_alpha_dummy_023 A R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_023, fv_syn_c0] using (nb066_compact_fv_empty_0002 A R)

theorem nb066_wpp_notmem_0035 (x : Var) (R : Class) : (nb066_alpha_dummy_026 x R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_026, fv_syn_c0] using (nb066_compact_fv_empty_0003 x R)

theorem nb066_wpp_notmem_0036 (A : Class) (R : Class) : (nb066_alpha_dummy_022 A R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_022, fv_syn_c0] using (nb066_compact_fv_empty_0004 A R)

theorem nb066_wpp_notmem_0037 (x : Var) (R : Class) : (nb066_alpha_dummy_025 x R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_025, fv_syn_c0] using (nb066_compact_fv_empty_0005 x R)

theorem nb066_wpp_notmem_0038 (A : Class) (R : Class) : (nb066_alpha_dummy_020 A R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_020, fv_syn_c0] using (nb066_compact_fv_empty_0006 A R)

theorem nb066_wpp_notmem_0039 (x : Var) (R : Class) : (nb066_alpha_dummy_021 x R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_021, fv_syn_c0] using (nb066_compact_fv_empty_0007 x R)

theorem nb066_wpp_notmem_0040 (A : Class) (R : Class) : (nb066_alpha_dummy_016 A R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_016, fv_syn_c0] using (nb066_compact_fv_empty_0008 A R)

theorem nb066_wpp_notmem_0041 (x : Var) (R : Class) : (nb066_alpha_dummy_018 x R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_018, fv_syn_c0] using (nb066_compact_fv_empty_0009 x R)

theorem nb066_wpp_notmem_0042 (A : Class) (R : Class) : (nb066_alpha_dummy_017 A R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_017, fv_syn_c0] using (nb066_compact_fv_empty_0010 A R)

theorem nb066_wpp_notmem_0043 (x : Var) (R : Class) : (nb066_alpha_dummy_019 x R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_019, fv_syn_c0] using (nb066_compact_fv_empty_0011 x R)

theorem nb066_wpp_notmem_0044 (A : Class) (R : Class) : (nb066_alpha_dummy_009 A R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_009, fv_syn_c0] using (nb066_compact_fv_empty_0012 A R)

theorem nb066_wpp_notmem_0045 (x : Var) (R : Class) : (nb066_alpha_dummy_011 x R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_011, fv_syn_c0] using (nb066_compact_fv_empty_0013 x R)

theorem nb066_wpp_notmem_0046 (A : Class) (R : Class) : (nb066_alpha_dummy_008 A R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_008, fv_syn_c0] using (nb066_compact_fv_empty_0014 A R)

theorem nb066_wpp_notmem_0047 (x : Var) (R : Class) : (nb066_alpha_dummy_010 x R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_010, fv_syn_c0] using (nb066_compact_fv_empty_0015 x R)

theorem nb066_wpp_notmem_0048 (A : Class) (R : Class) : (nb066_alpha_dummy_014 A R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_014, fv_syn_c0] using (nb066_compact_fv_empty_0016 A R)

theorem nb066_wpp_notmem_0049 (x : Var) (R : Class) : (nb066_alpha_dummy_015 x R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_015, fv_syn_c0] using (nb066_compact_fv_empty_0017 x R)

theorem nb066_wpp_notmem_0050 (A : Class) (R : Class) : (nb066_alpha_dummy_012 A R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_012, fv_syn_c0] using (nb066_compact_fv_empty_0018 A R)

theorem nb066_wpp_notmem_0051 (x : Var) (R : Class) : (nb066_alpha_dummy_013 x R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_013, fv_syn_c0] using (nb066_compact_fv_empty_0019 x R)

theorem nb066_wpp_notmem_0052 (A : Class) (R : Class) : (nb066_alpha_dummy_003 A R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_003, fv_syn_c0] using (nb066_compact_fv_empty_0020 A R)

theorem nb066_wpp_notmem_0053 (x : Var) (R : Class) : (nb066_alpha_dummy_005 x R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_005, fv_syn_c0] using (nb066_compact_fv_empty_0021 x R)

theorem nb066_wpp_notmem_0054 (A : Class) (R : Class) : (nb066_alpha_dummy_002 A R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_002, fv_syn_c0] using (nb066_compact_fv_empty_0022 A R)

theorem nb066_wpp_notmem_0055 (x : Var) (R : Class) : (nb066_alpha_dummy_004 x R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_004, fv_syn_c0] using (nb066_compact_fv_empty_0023 x R)

theorem nb066_wpp_notmem_0056 (A : Class) (R : Class) : (nb066_alpha_dummy_000 A R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_000, fv_syn_c0] using (nb066_compact_fv_empty_0024 A R)

theorem nb066_wpp_notmem_0057 (x : Var) : x ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb066_compact_fv_empty_0025 x)

theorem nb066_wpp_notmem_0058 (A : Class) (R : Class) : (nb066_alpha_dummy_001 A R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_001, fv_syn_c0] using (nb066_compact_fv_empty_0026 A R)

theorem nb066_wpp_notmem_0059 (y : Var) : y ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb066_compact_fv_empty_0027 y)

theorem nb066_compact_envfresh_0002 (x : Var) (y : Var) (A : Class) (R : Class) : TEnvFresh [((nb066_alpha_dummy_024 A R), (nb066_alpha_dummy_027 x R)), ((nb066_alpha_dummy_023 A R), (nb066_alpha_dummy_026 x R)), ((nb066_alpha_dummy_022 A R), (nb066_alpha_dummy_025 x R)), ((nb066_alpha_dummy_020 A R), (nb066_alpha_dummy_021 x R)), ((nb066_alpha_dummy_016 A R), (nb066_alpha_dummy_018 x R)), ((nb066_alpha_dummy_017 A R), (nb066_alpha_dummy_019 x R)), ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)), ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)), ((nb066_alpha_dummy_014 A R), (nb066_alpha_dummy_015 x R)), ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)), ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)), ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)), ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb066_alpha_dummy_024 A R) (nb066_alpha_dummy_027 x R) (nb066_wpp_notmem_0032 A R) (nb066_wpp_notmem_0033 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_023 A R) (nb066_alpha_dummy_026 x R) (nb066_wpp_notmem_0034 A R) (nb066_wpp_notmem_0035 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_022 A R) (nb066_alpha_dummy_025 x R) (nb066_wpp_notmem_0036 A R) (nb066_wpp_notmem_0037 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_020 A R) (nb066_alpha_dummy_021 x R) (nb066_wpp_notmem_0038 A R) (nb066_wpp_notmem_0039 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_016 A R) (nb066_alpha_dummy_018 x R) (nb066_wpp_notmem_0040 A R) (nb066_wpp_notmem_0041 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_017 A R) (nb066_alpha_dummy_019 x R) (nb066_wpp_notmem_0042 A R) (nb066_wpp_notmem_0043 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_009 A R) (nb066_alpha_dummy_011 x R) (nb066_wpp_notmem_0044 A R) (nb066_wpp_notmem_0045 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_008 A R) (nb066_alpha_dummy_010 x R) (nb066_wpp_notmem_0046 A R) (nb066_wpp_notmem_0047 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_014 A R) (nb066_alpha_dummy_015 x R) (nb066_wpp_notmem_0048 A R) (nb066_wpp_notmem_0049 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_012 A R) (nb066_alpha_dummy_013 x R) (nb066_wpp_notmem_0050 A R) (nb066_wpp_notmem_0051 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_003 A R) (nb066_alpha_dummy_005 x R) (nb066_wpp_notmem_0052 A R) (nb066_wpp_notmem_0053 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_002 A R) (nb066_alpha_dummy_004 x R) (nb066_wpp_notmem_0054 A R) (nb066_wpp_notmem_0055 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_000 A R) x (nb066_wpp_notmem_0056 A R) (nb066_wpp_notmem_0057 x) (TEnvFresh.consFresh (nb066_alpha_dummy_001 A R) y (nb066_wpp_notmem_0058 A R) (nb066_wpp_notmem_0059 y) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))

noncomputable def nb066_wpp_refl_0002 (x : Var) (y : Var) (A : Class) (R : Class) : TReflOn [((nb066_alpha_dummy_024 A R), (nb066_alpha_dummy_027 x R)), ((nb066_alpha_dummy_023 A R), (nb066_alpha_dummy_026 x R)), ((nb066_alpha_dummy_022 A R), (nb066_alpha_dummy_025 x R)), ((nb066_alpha_dummy_020 A R), (nb066_alpha_dummy_021 x R)), ((nb066_alpha_dummy_016 A R), (nb066_alpha_dummy_018 x R)), ((nb066_alpha_dummy_017 A R), (nb066_alpha_dummy_019 x R)), ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)), ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)), ((nb066_alpha_dummy_014 A R), (nb066_alpha_dummy_015 x R)), ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)), ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)), ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)), ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb066_compact_envfresh_0002 x y A R)

noncomputable def nb066_split_alpha_0000 (x : Var) (y : Var) (A : Class) (R : Class) : TAlphaWff [((nb066_alpha_dummy_024 A R), (nb066_alpha_dummy_027 x R)), ((nb066_alpha_dummy_023 A R), (nb066_alpha_dummy_026 x R)), ((nb066_alpha_dummy_022 A R), (nb066_alpha_dummy_025 x R)), ((nb066_alpha_dummy_020 A R), (nb066_alpha_dummy_021 x R)), ((nb066_alpha_dummy_016 A R), (nb066_alpha_dummy_018 x R)), ((nb066_alpha_dummy_017 A R), (nb066_alpha_dummy_019 x R)), ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)), ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)), ((nb066_alpha_dummy_014 A R), (nb066_alpha_dummy_015 x R)), ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)), ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)), ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)), ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb066_alpha_dummy_023 A R)) (Class.cv (nb066_alpha_dummy_024 A R))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb066_alpha_dummy_022 A R)) (syn_cun (Class.cv (nb066_alpha_dummy_023 A R)) (Class.cv (nb066_alpha_dummy_024 A R)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb066_alpha_dummy_026 x R)) (Class.cv (nb066_alpha_dummy_027 x R))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb066_alpha_dummy_025 x R)) (syn_cun (Class.cv (nb066_alpha_dummy_026 x R)) (Class.cv (nb066_alpha_dummy_027 x R)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0018 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0019 x R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0016 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0017 x R) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0022 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0023 x R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0020 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0021 x R) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0018 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0019 x R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0016 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0017 x R) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0022 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0023 x R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0020 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0021 x R) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb066_alpha_dummy_024 A R), (nb066_alpha_dummy_027 x R)), ((nb066_alpha_dummy_023 A R), (nb066_alpha_dummy_026 x R)), ((nb066_alpha_dummy_022 A R), (nb066_alpha_dummy_025 x R)), ((nb066_alpha_dummy_020 A R), (nb066_alpha_dummy_021 x R)), ((nb066_alpha_dummy_016 A R), (nb066_alpha_dummy_018 x R)), ((nb066_alpha_dummy_017 A R), (nb066_alpha_dummy_019 x R)), ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)), ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)), ((nb066_alpha_dummy_014 A R), (nb066_alpha_dummy_015 x R)), ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)), ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)), ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)), ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)] (syn_c0) (nb066_wpp_refl_0002 x y A R))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0026 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0027 x R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0024 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0025 x R) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0026 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0027 x R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0024 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0025 x R) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0030 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0031 x R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0028 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0029 x R) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0030 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0031 x R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0028 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0029 x R) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb066_wpp_notmem_0060 (A : Class) (R : Class) : (nb066_alpha_dummy_020 A R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb066_alpha_dummy_020, fv_syn_cnnc] using (nb066_compact_fv_empty_0006 A R)

theorem nb066_wpp_notmem_0061 (x : Var) (R : Class) : (nb066_alpha_dummy_021 x R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb066_alpha_dummy_021, fv_syn_cnnc] using (nb066_compact_fv_empty_0007 x R)

theorem nb066_wpp_notmem_0062 (A : Class) (R : Class) : (nb066_alpha_dummy_016 A R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb066_alpha_dummy_016, fv_syn_cnnc] using (nb066_compact_fv_empty_0008 A R)

theorem nb066_wpp_notmem_0063 (x : Var) (R : Class) : (nb066_alpha_dummy_018 x R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb066_alpha_dummy_018, fv_syn_cnnc] using (nb066_compact_fv_empty_0009 x R)

theorem nb066_wpp_notmem_0064 (A : Class) (R : Class) : (nb066_alpha_dummy_017 A R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb066_alpha_dummy_017, fv_syn_cnnc] using (nb066_compact_fv_empty_0010 A R)

theorem nb066_wpp_notmem_0065 (x : Var) (R : Class) : (nb066_alpha_dummy_019 x R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb066_alpha_dummy_019, fv_syn_cnnc] using (nb066_compact_fv_empty_0011 x R)

theorem nb066_wpp_notmem_0066 (A : Class) (R : Class) : (nb066_alpha_dummy_009 A R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb066_alpha_dummy_009, fv_syn_cnnc] using (nb066_compact_fv_empty_0012 A R)

theorem nb066_wpp_notmem_0067 (x : Var) (R : Class) : (nb066_alpha_dummy_011 x R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb066_alpha_dummy_011, fv_syn_cnnc] using (nb066_compact_fv_empty_0013 x R)

theorem nb066_wpp_notmem_0068 (A : Class) (R : Class) : (nb066_alpha_dummy_008 A R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb066_alpha_dummy_008, fv_syn_cnnc] using (nb066_compact_fv_empty_0014 A R)

theorem nb066_wpp_notmem_0069 (x : Var) (R : Class) : (nb066_alpha_dummy_010 x R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb066_alpha_dummy_010, fv_syn_cnnc] using (nb066_compact_fv_empty_0015 x R)

theorem nb066_wpp_notmem_0070 (A : Class) (R : Class) : (nb066_alpha_dummy_014 A R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb066_alpha_dummy_014, fv_syn_cnnc] using (nb066_compact_fv_empty_0016 A R)

theorem nb066_wpp_notmem_0071 (x : Var) (R : Class) : (nb066_alpha_dummy_015 x R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb066_alpha_dummy_015, fv_syn_cnnc] using (nb066_compact_fv_empty_0017 x R)

theorem nb066_wpp_notmem_0072 (A : Class) (R : Class) : (nb066_alpha_dummy_012 A R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb066_alpha_dummy_012, fv_syn_cnnc] using (nb066_compact_fv_empty_0018 A R)

theorem nb066_wpp_notmem_0073 (x : Var) (R : Class) : (nb066_alpha_dummy_013 x R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb066_alpha_dummy_013, fv_syn_cnnc] using (nb066_compact_fv_empty_0019 x R)

theorem nb066_wpp_notmem_0074 (A : Class) (R : Class) : (nb066_alpha_dummy_003 A R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb066_alpha_dummy_003, fv_syn_cnnc] using (nb066_compact_fv_empty_0020 A R)

theorem nb066_wpp_notmem_0075 (x : Var) (R : Class) : (nb066_alpha_dummy_005 x R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb066_alpha_dummy_005, fv_syn_cnnc] using (nb066_compact_fv_empty_0021 x R)

theorem nb066_wpp_notmem_0076 (A : Class) (R : Class) : (nb066_alpha_dummy_002 A R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb066_alpha_dummy_002, fv_syn_cnnc] using (nb066_compact_fv_empty_0022 A R)

theorem nb066_wpp_notmem_0077 (x : Var) (R : Class) : (nb066_alpha_dummy_004 x R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb066_alpha_dummy_004, fv_syn_cnnc] using (nb066_compact_fv_empty_0023 x R)

theorem nb066_wpp_notmem_0078 (A : Class) (R : Class) : (nb066_alpha_dummy_000 A R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb066_alpha_dummy_000, fv_syn_cnnc] using (nb066_compact_fv_empty_0024 A R)

theorem nb066_wpp_notmem_0079 (x : Var) : x ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb066_compact_fv_empty_0025 x)

theorem nb066_wpp_notmem_0080 (A : Class) (R : Class) : (nb066_alpha_dummy_001 A R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb066_alpha_dummy_001, fv_syn_cnnc] using (nb066_compact_fv_empty_0026 A R)

theorem nb066_wpp_notmem_0081 (y : Var) : y ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb066_compact_fv_empty_0027 y)

theorem nb066_compact_envfresh_0003 (x : Var) (y : Var) (A : Class) (R : Class) : TEnvFresh [((nb066_alpha_dummy_020 A R), (nb066_alpha_dummy_021 x R)), ((nb066_alpha_dummy_016 A R), (nb066_alpha_dummy_018 x R)), ((nb066_alpha_dummy_017 A R), (nb066_alpha_dummy_019 x R)), ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)), ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)), ((nb066_alpha_dummy_014 A R), (nb066_alpha_dummy_015 x R)), ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)), ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)), ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)), ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb066_alpha_dummy_020 A R) (nb066_alpha_dummy_021 x R) (nb066_wpp_notmem_0060 A R) (nb066_wpp_notmem_0061 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_016 A R) (nb066_alpha_dummy_018 x R) (nb066_wpp_notmem_0062 A R) (nb066_wpp_notmem_0063 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_017 A R) (nb066_alpha_dummy_019 x R) (nb066_wpp_notmem_0064 A R) (nb066_wpp_notmem_0065 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_009 A R) (nb066_alpha_dummy_011 x R) (nb066_wpp_notmem_0066 A R) (nb066_wpp_notmem_0067 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_008 A R) (nb066_alpha_dummy_010 x R) (nb066_wpp_notmem_0068 A R) (nb066_wpp_notmem_0069 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_014 A R) (nb066_alpha_dummy_015 x R) (nb066_wpp_notmem_0070 A R) (nb066_wpp_notmem_0071 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_012 A R) (nb066_alpha_dummy_013 x R) (nb066_wpp_notmem_0072 A R) (nb066_wpp_notmem_0073 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_003 A R) (nb066_alpha_dummy_005 x R) (nb066_wpp_notmem_0074 A R) (nb066_wpp_notmem_0075 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_002 A R) (nb066_alpha_dummy_004 x R) (nb066_wpp_notmem_0076 A R) (nb066_wpp_notmem_0077 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_000 A R) x (nb066_wpp_notmem_0078 A R) (nb066_wpp_notmem_0079 x) (TEnvFresh.consFresh (nb066_alpha_dummy_001 A R) y (nb066_wpp_notmem_0080 A R) (nb066_wpp_notmem_0081 y) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))

noncomputable def nb066_wpp_refl_0003 (x : Var) (y : Var) (A : Class) (R : Class) : TReflOn [((nb066_alpha_dummy_020 A R), (nb066_alpha_dummy_021 x R)), ((nb066_alpha_dummy_016 A R), (nb066_alpha_dummy_018 x R)), ((nb066_alpha_dummy_017 A R), (nb066_alpha_dummy_019 x R)), ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)), ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)), ((nb066_alpha_dummy_014 A R), (nb066_alpha_dummy_015 x R)), ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)), ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)), ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)), ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb066_compact_envfresh_0003 x y A R)

noncomputable def nb066_split_alpha_0001 (x : Var) (y : Var) (A : Class) (R : Class) : TAlphaWff [((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)), ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)), ((nb066_alpha_dummy_014 A R), (nb066_alpha_dummy_015 x R)), ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)), ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)), ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)), ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)] (Wff.imp (Wff.classMem (Class.cv (nb066_alpha_dummy_009 A R)) (Class.cv (nb066_alpha_dummy_003 A R))) (Wff.neg (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R)) (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))))) (Wff.imp (Wff.classMem (Class.cv (nb066_alpha_dummy_011 x R)) (Class.cv (nb066_alpha_dummy_005 x R))) (Wff.neg (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R)) (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0004 A R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0006 x R) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0004 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0006 x R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0008 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0009 x R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0005 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0007 x R) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb066_alpha_dummy_003 A R))).fv ∪ ((Class.cv (nb066_alpha_dummy_002 A R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb066_alpha_dummy_005 x R))).fv ∪ ((Class.cv (nb066_alpha_dummy_004 x R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0010 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0011 x R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0010 A R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0011 x R) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb066_alpha_dummy_009 A R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb066_alpha_dummy_011 x R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0014 A R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0015 x R) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0014 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0015 x R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0012 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0013 x R) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb066_alpha_dummy_024 A R), (nb066_alpha_dummy_027 x R)), ((nb066_alpha_dummy_023 A R), (nb066_alpha_dummy_026 x R)), ((nb066_alpha_dummy_022 A R), (nb066_alpha_dummy_025 x R)), ((nb066_alpha_dummy_020 A R), (nb066_alpha_dummy_021 x R)), ((nb066_alpha_dummy_016 A R), (nb066_alpha_dummy_018 x R)), ((nb066_alpha_dummy_017 A R), (nb066_alpha_dummy_019 x R)), ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)), ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)), ((nb066_alpha_dummy_014 A R), (nb066_alpha_dummy_015 x R)), ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)), ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)), ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)), ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)] (syn_c1c) (nb066_wpp_refl_0001 x y A R))) (TAlphaWff.neg (TAlphaWff.neg (nb066_split_alpha_0000 x y A R)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0012 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0013 x R) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb066_alpha_dummy_020 A R), (nb066_alpha_dummy_021 x R)), ((nb066_alpha_dummy_016 A R), (nb066_alpha_dummy_018 x R)), ((nb066_alpha_dummy_017 A R), (nb066_alpha_dummy_019 x R)), ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)), ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)), ((nb066_alpha_dummy_014 A R), (nb066_alpha_dummy_015 x R)), ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)), ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)), ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)), ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)] (syn_cnnc) (nb066_wpp_refl_0003 x y A R))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0012 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0013 x R) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0012 A R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0013 x R) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb066_alpha_dummy_020 A R), (nb066_alpha_dummy_021 x R)), ((nb066_alpha_dummy_016 A R), (nb066_alpha_dummy_018 x R)), ((nb066_alpha_dummy_017 A R), (nb066_alpha_dummy_019 x R)), ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)), ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)), ((nb066_alpha_dummy_014 A R), (nb066_alpha_dummy_015 x R)), ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)), ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)), ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)), ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)] (syn_cnnc) (nb066_wpp_refl_0003 x y A R))))))))))))))))))))

theorem nb066_compact_fv_empty_0028 (A : Class) (R : Class) : (nb066_alpha_dummy_042 A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0082 (A : Class) (R : Class) : (nb066_alpha_dummy_042 A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_042, fv_syn_c1c] using (nb066_compact_fv_empty_0028 A R)

theorem nb066_compact_fv_empty_0029 (x : Var) (R : Class) : (nb066_alpha_dummy_043 x R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0083 (x : Var) (R : Class) : (nb066_alpha_dummy_043 x R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_043, fv_syn_c1c] using (nb066_compact_fv_empty_0029 x R)

theorem nb066_compact_fv_empty_0030 (A : Class) (R : Class) : (nb066_alpha_dummy_040 A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0084 (A : Class) (R : Class) : (nb066_alpha_dummy_040 A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_040, fv_syn_c1c] using (nb066_compact_fv_empty_0030 A R)

theorem nb066_compact_fv_empty_0031 (x : Var) (R : Class) : (nb066_alpha_dummy_041 x R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0085 (x : Var) (R : Class) : (nb066_alpha_dummy_041 x R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_041, fv_syn_c1c] using (nb066_compact_fv_empty_0031 x R)

theorem nb066_compact_fv_empty_0032 (A : Class) (R : Class) : (nb066_alpha_dummy_038 A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0086 (A : Class) (R : Class) : (nb066_alpha_dummy_038 A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_038, fv_syn_c1c] using (nb066_compact_fv_empty_0032 A R)

theorem nb066_compact_fv_empty_0033 (x : Var) (R : Class) : (nb066_alpha_dummy_039 x R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb066_wpp_notmem_0087 (x : Var) (R : Class) : (nb066_alpha_dummy_039 x R) ∉ ((syn_c1c)).fv := by
  simpa only [nb066_alpha_dummy_039, fv_syn_c1c] using (nb066_compact_fv_empty_0033 x R)

theorem nb066_compact_envfresh_0004 (x : Var) (y : Var) (A : Class) (R : Class) : TEnvFresh [((nb066_alpha_dummy_024 A R), (nb066_alpha_dummy_027 x R)), ((nb066_alpha_dummy_023 A R), (nb066_alpha_dummy_026 x R)), ((nb066_alpha_dummy_022 A R), (nb066_alpha_dummy_025 x R)), ((nb066_alpha_dummy_020 A R), (nb066_alpha_dummy_021 x R)), ((nb066_alpha_dummy_016 A R), (nb066_alpha_dummy_018 x R)), ((nb066_alpha_dummy_017 A R), (nb066_alpha_dummy_019 x R)), ((nb066_alpha_dummy_042 A R), (nb066_alpha_dummy_043 x R)), ((nb066_alpha_dummy_040 A R), (nb066_alpha_dummy_041 x R)), ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)), ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)), ((nb066_alpha_dummy_038 A R), (nb066_alpha_dummy_039 x R)), ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)), ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)), ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)), ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb066_alpha_dummy_024 A R) (nb066_alpha_dummy_027 x R) (nb066_wpp_notmem_0004 A R) (nb066_wpp_notmem_0005 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_023 A R) (nb066_alpha_dummy_026 x R) (nb066_wpp_notmem_0006 A R) (nb066_wpp_notmem_0007 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_022 A R) (nb066_alpha_dummy_025 x R) (nb066_wpp_notmem_0008 A R) (nb066_wpp_notmem_0009 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_020 A R) (nb066_alpha_dummy_021 x R) (nb066_wpp_notmem_0010 A R) (nb066_wpp_notmem_0011 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_016 A R) (nb066_alpha_dummy_018 x R) (nb066_wpp_notmem_0012 A R) (nb066_wpp_notmem_0013 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_017 A R) (nb066_alpha_dummy_019 x R) (nb066_wpp_notmem_0014 A R) (nb066_wpp_notmem_0015 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_042 A R) (nb066_alpha_dummy_043 x R) (nb066_wpp_notmem_0082 A R) (nb066_wpp_notmem_0083 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_040 A R) (nb066_alpha_dummy_041 x R) (nb066_wpp_notmem_0084 A R) (nb066_wpp_notmem_0085 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_009 A R) (nb066_alpha_dummy_011 x R) (nb066_wpp_notmem_0016 A R) (nb066_wpp_notmem_0017 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_008 A R) (nb066_alpha_dummy_010 x R) (nb066_wpp_notmem_0018 A R) (nb066_wpp_notmem_0019 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_038 A R) (nb066_alpha_dummy_039 x R) (nb066_wpp_notmem_0086 A R) (nb066_wpp_notmem_0087 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_012 A R) (nb066_alpha_dummy_013 x R) (nb066_wpp_notmem_0022 A R) (nb066_wpp_notmem_0023 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_003 A R) (nb066_alpha_dummy_005 x R) (nb066_wpp_notmem_0024 A R) (nb066_wpp_notmem_0025 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_002 A R) (nb066_alpha_dummy_004 x R) (nb066_wpp_notmem_0026 A R) (nb066_wpp_notmem_0027 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_000 A R) x (nb066_wpp_notmem_0028 A R) (nb066_wpp_notmem_0029 x) (TEnvFresh.consFresh (nb066_alpha_dummy_001 A R) y (nb066_wpp_notmem_0030 A R) (nb066_wpp_notmem_0031 y) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))

noncomputable def nb066_wpp_refl_0004 (x : Var) (y : Var) (A : Class) (R : Class) : TReflOn [((nb066_alpha_dummy_024 A R), (nb066_alpha_dummy_027 x R)), ((nb066_alpha_dummy_023 A R), (nb066_alpha_dummy_026 x R)), ((nb066_alpha_dummy_022 A R), (nb066_alpha_dummy_025 x R)), ((nb066_alpha_dummy_020 A R), (nb066_alpha_dummy_021 x R)), ((nb066_alpha_dummy_016 A R), (nb066_alpha_dummy_018 x R)), ((nb066_alpha_dummy_017 A R), (nb066_alpha_dummy_019 x R)), ((nb066_alpha_dummy_042 A R), (nb066_alpha_dummy_043 x R)), ((nb066_alpha_dummy_040 A R), (nb066_alpha_dummy_041 x R)), ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)), ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)), ((nb066_alpha_dummy_038 A R), (nb066_alpha_dummy_039 x R)), ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)), ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)), ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)), ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb066_compact_envfresh_0004 x y A R)

theorem nb066_wpp_notmem_0088 (A : Class) (R : Class) : (nb066_alpha_dummy_042 A R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_042, fv_syn_c0] using (nb066_compact_fv_empty_0028 A R)

theorem nb066_wpp_notmem_0089 (x : Var) (R : Class) : (nb066_alpha_dummy_043 x R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_043, fv_syn_c0] using (nb066_compact_fv_empty_0029 x R)

theorem nb066_wpp_notmem_0090 (A : Class) (R : Class) : (nb066_alpha_dummy_040 A R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_040, fv_syn_c0] using (nb066_compact_fv_empty_0030 A R)

theorem nb066_wpp_notmem_0091 (x : Var) (R : Class) : (nb066_alpha_dummy_041 x R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_041, fv_syn_c0] using (nb066_compact_fv_empty_0031 x R)

theorem nb066_wpp_notmem_0092 (A : Class) (R : Class) : (nb066_alpha_dummy_038 A R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_038, fv_syn_c0] using (nb066_compact_fv_empty_0032 A R)

theorem nb066_wpp_notmem_0093 (x : Var) (R : Class) : (nb066_alpha_dummy_039 x R) ∉ ((syn_c0)).fv := by
  simpa only [nb066_alpha_dummy_039, fv_syn_c0] using (nb066_compact_fv_empty_0033 x R)

theorem nb066_compact_envfresh_0005 (x : Var) (y : Var) (A : Class) (R : Class) : TEnvFresh [((nb066_alpha_dummy_024 A R), (nb066_alpha_dummy_027 x R)), ((nb066_alpha_dummy_023 A R), (nb066_alpha_dummy_026 x R)), ((nb066_alpha_dummy_022 A R), (nb066_alpha_dummy_025 x R)), ((nb066_alpha_dummy_020 A R), (nb066_alpha_dummy_021 x R)), ((nb066_alpha_dummy_016 A R), (nb066_alpha_dummy_018 x R)), ((nb066_alpha_dummy_017 A R), (nb066_alpha_dummy_019 x R)), ((nb066_alpha_dummy_042 A R), (nb066_alpha_dummy_043 x R)), ((nb066_alpha_dummy_040 A R), (nb066_alpha_dummy_041 x R)), ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)), ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)), ((nb066_alpha_dummy_038 A R), (nb066_alpha_dummy_039 x R)), ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)), ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)), ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)), ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb066_alpha_dummy_024 A R) (nb066_alpha_dummy_027 x R) (nb066_wpp_notmem_0032 A R) (nb066_wpp_notmem_0033 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_023 A R) (nb066_alpha_dummy_026 x R) (nb066_wpp_notmem_0034 A R) (nb066_wpp_notmem_0035 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_022 A R) (nb066_alpha_dummy_025 x R) (nb066_wpp_notmem_0036 A R) (nb066_wpp_notmem_0037 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_020 A R) (nb066_alpha_dummy_021 x R) (nb066_wpp_notmem_0038 A R) (nb066_wpp_notmem_0039 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_016 A R) (nb066_alpha_dummy_018 x R) (nb066_wpp_notmem_0040 A R) (nb066_wpp_notmem_0041 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_017 A R) (nb066_alpha_dummy_019 x R) (nb066_wpp_notmem_0042 A R) (nb066_wpp_notmem_0043 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_042 A R) (nb066_alpha_dummy_043 x R) (nb066_wpp_notmem_0088 A R) (nb066_wpp_notmem_0089 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_040 A R) (nb066_alpha_dummy_041 x R) (nb066_wpp_notmem_0090 A R) (nb066_wpp_notmem_0091 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_009 A R) (nb066_alpha_dummy_011 x R) (nb066_wpp_notmem_0044 A R) (nb066_wpp_notmem_0045 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_008 A R) (nb066_alpha_dummy_010 x R) (nb066_wpp_notmem_0046 A R) (nb066_wpp_notmem_0047 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_038 A R) (nb066_alpha_dummy_039 x R) (nb066_wpp_notmem_0092 A R) (nb066_wpp_notmem_0093 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_012 A R) (nb066_alpha_dummy_013 x R) (nb066_wpp_notmem_0050 A R) (nb066_wpp_notmem_0051 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_003 A R) (nb066_alpha_dummy_005 x R) (nb066_wpp_notmem_0052 A R) (nb066_wpp_notmem_0053 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_002 A R) (nb066_alpha_dummy_004 x R) (nb066_wpp_notmem_0054 A R) (nb066_wpp_notmem_0055 x R) (TEnvFresh.consFresh (nb066_alpha_dummy_000 A R) x (nb066_wpp_notmem_0056 A R) (nb066_wpp_notmem_0057 x) (TEnvFresh.consFresh (nb066_alpha_dummy_001 A R) y (nb066_wpp_notmem_0058 A R) (nb066_wpp_notmem_0059 y) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))

noncomputable def nb066_wpp_refl_0005 (x : Var) (y : Var) (A : Class) (R : Class) : TReflOn [((nb066_alpha_dummy_024 A R), (nb066_alpha_dummy_027 x R)), ((nb066_alpha_dummy_023 A R), (nb066_alpha_dummy_026 x R)), ((nb066_alpha_dummy_022 A R), (nb066_alpha_dummy_025 x R)), ((nb066_alpha_dummy_020 A R), (nb066_alpha_dummy_021 x R)), ((nb066_alpha_dummy_016 A R), (nb066_alpha_dummy_018 x R)), ((nb066_alpha_dummy_017 A R), (nb066_alpha_dummy_019 x R)), ((nb066_alpha_dummy_042 A R), (nb066_alpha_dummy_043 x R)), ((nb066_alpha_dummy_040 A R), (nb066_alpha_dummy_041 x R)), ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)), ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)), ((nb066_alpha_dummy_038 A R), (nb066_alpha_dummy_039 x R)), ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)), ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)), ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)), ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb066_compact_envfresh_0005 x y A R)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
