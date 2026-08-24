import NAR4C089C001Part002

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

theorem nb089_compact_fv_empty_0000 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_023 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0000 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_023 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_023, fv_syn_c1c] using (nb089_compact_fv_empty_0000 A B R)

theorem nb089_compact_fv_empty_0001 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_026 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0001 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_026 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_026, fv_syn_c1c] using (nb089_compact_fv_empty_0001 u A B R)

theorem nb089_compact_fv_empty_0002 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_022 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0002 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_022 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_022, fv_syn_c1c] using (nb089_compact_fv_empty_0002 A B R)

theorem nb089_compact_fv_empty_0003 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_025 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0003 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_025 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_025, fv_syn_c1c] using (nb089_compact_fv_empty_0003 u A B R)

theorem nb089_compact_fv_empty_0004 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_021 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0004 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_021 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_021, fv_syn_c1c] using (nb089_compact_fv_empty_0004 A B R)

theorem nb089_compact_fv_empty_0005 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_024 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0005 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_024 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_024, fv_syn_c1c] using (nb089_compact_fv_empty_0005 u A B R)

theorem nb089_compact_fv_empty_0006 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_019 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0006 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_019 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_019, fv_syn_c1c] using (nb089_compact_fv_empty_0006 A B R)

theorem nb089_compact_fv_empty_0007 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_020 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0007 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_020 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_020, fv_syn_c1c] using (nb089_compact_fv_empty_0007 u A B R)

theorem nb089_compact_fv_empty_0008 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_015 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0008 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_015 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_015, fv_syn_c1c] using (nb089_compact_fv_empty_0008 A B R)

theorem nb089_compact_fv_empty_0009 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_017 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0009 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_017 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_017, fv_syn_c1c] using (nb089_compact_fv_empty_0009 u A B R)

theorem nb089_compact_fv_empty_0010 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_016 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0010 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_016 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_016, fv_syn_c1c] using (nb089_compact_fv_empty_0010 A B R)

theorem nb089_compact_fv_empty_0011 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_018 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0011 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_018 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_018, fv_syn_c1c] using (nb089_compact_fv_empty_0011 u A B R)

theorem nb089_compact_fv_empty_0012 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_008 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0012 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_008 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_008, fv_syn_c1c] using (nb089_compact_fv_empty_0012 A B R)

theorem nb089_compact_fv_empty_0013 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_010 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0013 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_010 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_010, fv_syn_c1c] using (nb089_compact_fv_empty_0013 u A B R)

theorem nb089_compact_fv_empty_0014 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_007 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0014 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_007 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_007, fv_syn_c1c] using (nb089_compact_fv_empty_0014 A B R)

theorem nb089_compact_fv_empty_0015 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_009 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0015 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_009 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_009, fv_syn_c1c] using (nb089_compact_fv_empty_0015 u A B R)

theorem nb089_compact_fv_empty_0016 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_013 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0016 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_013 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_013, fv_syn_c1c] using (nb089_compact_fv_empty_0016 A B R)

theorem nb089_compact_fv_empty_0017 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_014 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0017 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_014 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_014, fv_syn_c1c] using (nb089_compact_fv_empty_0017 u A B R)

theorem nb089_compact_fv_empty_0018 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_011 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0018 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_011 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_011, fv_syn_c1c] using (nb089_compact_fv_empty_0018 A B R)

theorem nb089_compact_fv_empty_0019 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_012 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0019 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_012 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_012, fv_syn_c1c] using (nb089_compact_fv_empty_0019 u A B R)

theorem nb089_compact_fv_empty_0020 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_003 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0020 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_003 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_003, fv_syn_c1c] using (nb089_compact_fv_empty_0020 A B R)

theorem nb089_compact_fv_empty_0021 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_004 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0021 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_004 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_004, fv_syn_c1c] using (nb089_compact_fv_empty_0021 u A B R)

theorem nb089_compact_fv_empty_0022 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_000 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0022 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_000 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_000, fv_syn_c1c] using (nb089_compact_fv_empty_0022 A B R)

theorem nb089_compact_fv_empty_0023 (u : Var) : u ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0023 (u : Var) : u ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb089_compact_fv_empty_0023 u)

theorem nb089_compact_fv_empty_0024 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_005 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0024 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_005 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_005, fv_syn_c1c] using (nb089_compact_fv_empty_0024 A B R)

theorem nb089_compact_fv_empty_0025 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_006 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0025 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_006 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_006, fv_syn_c1c] using (nb089_compact_fv_empty_0025 u A B R)

theorem nb089_compact_fv_empty_0026 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_001 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0026 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_001 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_001, fv_syn_c1c] using (nb089_compact_fv_empty_0026 A B R)

theorem nb089_compact_fv_empty_0027 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_002 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0027 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_002 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_002, fv_syn_c1c] using (nb089_compact_fv_empty_0027 u A B R)

theorem nb089_compact_envfresh_0000 (u : Var) (A : Class) (B : Class) (R : Class) : TEnvFresh [((nb089_alpha_dummy_023 A B R), (nb089_alpha_dummy_026 u A B R)), ((nb089_alpha_dummy_022 A B R), (nb089_alpha_dummy_025 u A B R)), ((nb089_alpha_dummy_021 A B R), (nb089_alpha_dummy_024 u A B R)), ((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)), ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)), ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)), ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)), ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)), ((nb089_alpha_dummy_013 A B R), (nb089_alpha_dummy_014 u A B R)), ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb089_alpha_dummy_023 A B R) (nb089_alpha_dummy_026 u A B R) (nb089_wpp_notmem_0000 A B R) (nb089_wpp_notmem_0001 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_022 A B R) (nb089_alpha_dummy_025 u A B R) (nb089_wpp_notmem_0002 A B R) (nb089_wpp_notmem_0003 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_021 A B R) (nb089_alpha_dummy_024 u A B R) (nb089_wpp_notmem_0004 A B R) (nb089_wpp_notmem_0005 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_019 A B R) (nb089_alpha_dummy_020 u A B R) (nb089_wpp_notmem_0006 A B R) (nb089_wpp_notmem_0007 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_015 A B R) (nb089_alpha_dummy_017 u A B R) (nb089_wpp_notmem_0008 A B R) (nb089_wpp_notmem_0009 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_016 A B R) (nb089_alpha_dummy_018 u A B R) (nb089_wpp_notmem_0010 A B R) (nb089_wpp_notmem_0011 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_008 A B R) (nb089_alpha_dummy_010 u A B R) (nb089_wpp_notmem_0012 A B R) (nb089_wpp_notmem_0013 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_007 A B R) (nb089_alpha_dummy_009 u A B R) (nb089_wpp_notmem_0014 A B R) (nb089_wpp_notmem_0015 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_013 A B R) (nb089_alpha_dummy_014 u A B R) (nb089_wpp_notmem_0016 A B R) (nb089_wpp_notmem_0017 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_011 A B R) (nb089_alpha_dummy_012 u A B R) (nb089_wpp_notmem_0018 A B R) (nb089_wpp_notmem_0019 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_003 A B R) (nb089_alpha_dummy_004 u A B R) (nb089_wpp_notmem_0020 A B R) (nb089_wpp_notmem_0021 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_000 A B R) u (nb089_wpp_notmem_0022 A B R) (nb089_wpp_notmem_0023 u) (TEnvFresh.consFresh (nb089_alpha_dummy_005 A B R) (nb089_alpha_dummy_006 u A B R) (nb089_wpp_notmem_0024 A B R) (nb089_wpp_notmem_0025 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_001 A B R) (nb089_alpha_dummy_002 u A B R) (nb089_wpp_notmem_0026 A B R) (nb089_wpp_notmem_0027 u A B R) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))

noncomputable def nb089_wpp_refl_0000 (u : Var) (A : Class) (B : Class) (R : Class) : TReflOn [((nb089_alpha_dummy_023 A B R), (nb089_alpha_dummy_026 u A B R)), ((nb089_alpha_dummy_022 A B R), (nb089_alpha_dummy_025 u A B R)), ((nb089_alpha_dummy_021 A B R), (nb089_alpha_dummy_024 u A B R)), ((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)), ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)), ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)), ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)), ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)), ((nb089_alpha_dummy_013 A B R), (nb089_alpha_dummy_014 u A B R)), ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb089_compact_envfresh_0000 u A B R)

theorem nb089_wpp_notmem_0028 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_023 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_023, fv_syn_c0] using (nb089_compact_fv_empty_0000 A B R)

theorem nb089_wpp_notmem_0029 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_026 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_026, fv_syn_c0] using (nb089_compact_fv_empty_0001 u A B R)

theorem nb089_wpp_notmem_0030 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_022 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_022, fv_syn_c0] using (nb089_compact_fv_empty_0002 A B R)

theorem nb089_wpp_notmem_0031 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_025 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_025, fv_syn_c0] using (nb089_compact_fv_empty_0003 u A B R)

theorem nb089_wpp_notmem_0032 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_021 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_021, fv_syn_c0] using (nb089_compact_fv_empty_0004 A B R)

theorem nb089_wpp_notmem_0033 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_024 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_024, fv_syn_c0] using (nb089_compact_fv_empty_0005 u A B R)

theorem nb089_wpp_notmem_0034 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_019 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_019, fv_syn_c0] using (nb089_compact_fv_empty_0006 A B R)

theorem nb089_wpp_notmem_0035 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_020 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_020, fv_syn_c0] using (nb089_compact_fv_empty_0007 u A B R)

theorem nb089_wpp_notmem_0036 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_015 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_015, fv_syn_c0] using (nb089_compact_fv_empty_0008 A B R)

theorem nb089_wpp_notmem_0037 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_017 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_017, fv_syn_c0] using (nb089_compact_fv_empty_0009 u A B R)

theorem nb089_wpp_notmem_0038 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_016 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_016, fv_syn_c0] using (nb089_compact_fv_empty_0010 A B R)

theorem nb089_wpp_notmem_0039 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_018 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_018, fv_syn_c0] using (nb089_compact_fv_empty_0011 u A B R)

theorem nb089_wpp_notmem_0040 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_008 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_008, fv_syn_c0] using (nb089_compact_fv_empty_0012 A B R)

theorem nb089_wpp_notmem_0041 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_010 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_010, fv_syn_c0] using (nb089_compact_fv_empty_0013 u A B R)

theorem nb089_wpp_notmem_0042 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_007 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_007, fv_syn_c0] using (nb089_compact_fv_empty_0014 A B R)

theorem nb089_wpp_notmem_0043 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_009 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_009, fv_syn_c0] using (nb089_compact_fv_empty_0015 u A B R)

theorem nb089_wpp_notmem_0044 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_013 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_013, fv_syn_c0] using (nb089_compact_fv_empty_0016 A B R)

theorem nb089_wpp_notmem_0045 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_014 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_014, fv_syn_c0] using (nb089_compact_fv_empty_0017 u A B R)

theorem nb089_wpp_notmem_0046 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_011 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_011, fv_syn_c0] using (nb089_compact_fv_empty_0018 A B R)

theorem nb089_wpp_notmem_0047 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_012 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_012, fv_syn_c0] using (nb089_compact_fv_empty_0019 u A B R)

theorem nb089_wpp_notmem_0048 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_003 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_003, fv_syn_c0] using (nb089_compact_fv_empty_0020 A B R)

theorem nb089_wpp_notmem_0049 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_004 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_004, fv_syn_c0] using (nb089_compact_fv_empty_0021 u A B R)

theorem nb089_wpp_notmem_0050 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_000 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_000, fv_syn_c0] using (nb089_compact_fv_empty_0022 A B R)

theorem nb089_wpp_notmem_0051 (u : Var) : u ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb089_compact_fv_empty_0023 u)

theorem nb089_wpp_notmem_0052 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_005 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_005, fv_syn_c0] using (nb089_compact_fv_empty_0024 A B R)

theorem nb089_wpp_notmem_0053 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_006 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_006, fv_syn_c0] using (nb089_compact_fv_empty_0025 u A B R)

theorem nb089_wpp_notmem_0054 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_001 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_001, fv_syn_c0] using (nb089_compact_fv_empty_0026 A B R)

theorem nb089_wpp_notmem_0055 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_002 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_002, fv_syn_c0] using (nb089_compact_fv_empty_0027 u A B R)

theorem nb089_compact_envfresh_0001 (u : Var) (A : Class) (B : Class) (R : Class) : TEnvFresh [((nb089_alpha_dummy_023 A B R), (nb089_alpha_dummy_026 u A B R)), ((nb089_alpha_dummy_022 A B R), (nb089_alpha_dummy_025 u A B R)), ((nb089_alpha_dummy_021 A B R), (nb089_alpha_dummy_024 u A B R)), ((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)), ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)), ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)), ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)), ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)), ((nb089_alpha_dummy_013 A B R), (nb089_alpha_dummy_014 u A B R)), ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb089_alpha_dummy_023 A B R) (nb089_alpha_dummy_026 u A B R) (nb089_wpp_notmem_0028 A B R) (nb089_wpp_notmem_0029 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_022 A B R) (nb089_alpha_dummy_025 u A B R) (nb089_wpp_notmem_0030 A B R) (nb089_wpp_notmem_0031 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_021 A B R) (nb089_alpha_dummy_024 u A B R) (nb089_wpp_notmem_0032 A B R) (nb089_wpp_notmem_0033 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_019 A B R) (nb089_alpha_dummy_020 u A B R) (nb089_wpp_notmem_0034 A B R) (nb089_wpp_notmem_0035 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_015 A B R) (nb089_alpha_dummy_017 u A B R) (nb089_wpp_notmem_0036 A B R) (nb089_wpp_notmem_0037 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_016 A B R) (nb089_alpha_dummy_018 u A B R) (nb089_wpp_notmem_0038 A B R) (nb089_wpp_notmem_0039 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_008 A B R) (nb089_alpha_dummy_010 u A B R) (nb089_wpp_notmem_0040 A B R) (nb089_wpp_notmem_0041 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_007 A B R) (nb089_alpha_dummy_009 u A B R) (nb089_wpp_notmem_0042 A B R) (nb089_wpp_notmem_0043 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_013 A B R) (nb089_alpha_dummy_014 u A B R) (nb089_wpp_notmem_0044 A B R) (nb089_wpp_notmem_0045 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_011 A B R) (nb089_alpha_dummy_012 u A B R) (nb089_wpp_notmem_0046 A B R) (nb089_wpp_notmem_0047 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_003 A B R) (nb089_alpha_dummy_004 u A B R) (nb089_wpp_notmem_0048 A B R) (nb089_wpp_notmem_0049 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_000 A B R) u (nb089_wpp_notmem_0050 A B R) (nb089_wpp_notmem_0051 u) (TEnvFresh.consFresh (nb089_alpha_dummy_005 A B R) (nb089_alpha_dummy_006 u A B R) (nb089_wpp_notmem_0052 A B R) (nb089_wpp_notmem_0053 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_001 A B R) (nb089_alpha_dummy_002 u A B R) (nb089_wpp_notmem_0054 A B R) (nb089_wpp_notmem_0055 u A B R) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))

noncomputable def nb089_wpp_refl_0001 (u : Var) (A : Class) (B : Class) (R : Class) : TReflOn [((nb089_alpha_dummy_023 A B R), (nb089_alpha_dummy_026 u A B R)), ((nb089_alpha_dummy_022 A B R), (nb089_alpha_dummy_025 u A B R)), ((nb089_alpha_dummy_021 A B R), (nb089_alpha_dummy_024 u A B R)), ((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)), ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)), ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)), ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)), ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)), ((nb089_alpha_dummy_013 A B R), (nb089_alpha_dummy_014 u A B R)), ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb089_compact_envfresh_0001 u A B R)

theorem nb089_wpp_notmem_0056 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_019 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_019, fv_syn_cnnc] using (nb089_compact_fv_empty_0006 A B R)

theorem nb089_wpp_notmem_0057 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_020 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_020, fv_syn_cnnc] using (nb089_compact_fv_empty_0007 u A B R)

theorem nb089_wpp_notmem_0058 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_015 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_015, fv_syn_cnnc] using (nb089_compact_fv_empty_0008 A B R)

theorem nb089_wpp_notmem_0059 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_017 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_017, fv_syn_cnnc] using (nb089_compact_fv_empty_0009 u A B R)

theorem nb089_wpp_notmem_0060 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_016 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_016, fv_syn_cnnc] using (nb089_compact_fv_empty_0010 A B R)

theorem nb089_wpp_notmem_0061 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_018 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_018, fv_syn_cnnc] using (nb089_compact_fv_empty_0011 u A B R)

theorem nb089_wpp_notmem_0062 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_008 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_008, fv_syn_cnnc] using (nb089_compact_fv_empty_0012 A B R)

theorem nb089_wpp_notmem_0063 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_010 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_010, fv_syn_cnnc] using (nb089_compact_fv_empty_0013 u A B R)

theorem nb089_wpp_notmem_0064 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_007 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_007, fv_syn_cnnc] using (nb089_compact_fv_empty_0014 A B R)

theorem nb089_wpp_notmem_0065 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_009 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_009, fv_syn_cnnc] using (nb089_compact_fv_empty_0015 u A B R)

theorem nb089_wpp_notmem_0066 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_013 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_013, fv_syn_cnnc] using (nb089_compact_fv_empty_0016 A B R)

theorem nb089_wpp_notmem_0067 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_014 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_014, fv_syn_cnnc] using (nb089_compact_fv_empty_0017 u A B R)

theorem nb089_wpp_notmem_0068 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_011 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_011, fv_syn_cnnc] using (nb089_compact_fv_empty_0018 A B R)

theorem nb089_wpp_notmem_0069 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_012 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_012, fv_syn_cnnc] using (nb089_compact_fv_empty_0019 u A B R)

theorem nb089_wpp_notmem_0070 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_003 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_003, fv_syn_cnnc] using (nb089_compact_fv_empty_0020 A B R)

theorem nb089_wpp_notmem_0071 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_004 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_004, fv_syn_cnnc] using (nb089_compact_fv_empty_0021 u A B R)

theorem nb089_wpp_notmem_0072 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_000 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_000, fv_syn_cnnc] using (nb089_compact_fv_empty_0022 A B R)

theorem nb089_wpp_notmem_0073 (u : Var) : u ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb089_compact_fv_empty_0023 u)

theorem nb089_wpp_notmem_0074 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_005 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_005, fv_syn_cnnc] using (nb089_compact_fv_empty_0024 A B R)

theorem nb089_wpp_notmem_0075 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_006 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_006, fv_syn_cnnc] using (nb089_compact_fv_empty_0025 u A B R)

theorem nb089_wpp_notmem_0076 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_001 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_001, fv_syn_cnnc] using (nb089_compact_fv_empty_0026 A B R)

theorem nb089_wpp_notmem_0077 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_002 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_002, fv_syn_cnnc] using (nb089_compact_fv_empty_0027 u A B R)

theorem nb089_compact_envfresh_0002 (u : Var) (A : Class) (B : Class) (R : Class) : TEnvFresh [((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)), ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)), ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)), ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)), ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)), ((nb089_alpha_dummy_013 A B R), (nb089_alpha_dummy_014 u A B R)), ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb089_alpha_dummy_019 A B R) (nb089_alpha_dummy_020 u A B R) (nb089_wpp_notmem_0056 A B R) (nb089_wpp_notmem_0057 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_015 A B R) (nb089_alpha_dummy_017 u A B R) (nb089_wpp_notmem_0058 A B R) (nb089_wpp_notmem_0059 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_016 A B R) (nb089_alpha_dummy_018 u A B R) (nb089_wpp_notmem_0060 A B R) (nb089_wpp_notmem_0061 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_008 A B R) (nb089_alpha_dummy_010 u A B R) (nb089_wpp_notmem_0062 A B R) (nb089_wpp_notmem_0063 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_007 A B R) (nb089_alpha_dummy_009 u A B R) (nb089_wpp_notmem_0064 A B R) (nb089_wpp_notmem_0065 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_013 A B R) (nb089_alpha_dummy_014 u A B R) (nb089_wpp_notmem_0066 A B R) (nb089_wpp_notmem_0067 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_011 A B R) (nb089_alpha_dummy_012 u A B R) (nb089_wpp_notmem_0068 A B R) (nb089_wpp_notmem_0069 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_003 A B R) (nb089_alpha_dummy_004 u A B R) (nb089_wpp_notmem_0070 A B R) (nb089_wpp_notmem_0071 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_000 A B R) u (nb089_wpp_notmem_0072 A B R) (nb089_wpp_notmem_0073 u) (TEnvFresh.consFresh (nb089_alpha_dummy_005 A B R) (nb089_alpha_dummy_006 u A B R) (nb089_wpp_notmem_0074 A B R) (nb089_wpp_notmem_0075 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_001 A B R) (nb089_alpha_dummy_002 u A B R) (nb089_wpp_notmem_0076 A B R) (nb089_wpp_notmem_0077 u A B R) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))

noncomputable def nb089_wpp_refl_0002 (u : Var) (A : Class) (B : Class) (R : Class) : TReflOn [((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)), ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)), ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)), ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)), ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)), ((nb089_alpha_dummy_013 A B R), (nb089_alpha_dummy_014 u A B R)), ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb089_compact_envfresh_0002 u A B R)

theorem nb089_compact_fv_empty_0028 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_041 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0078 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_041 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_041, fv_syn_c1c] using (nb089_compact_fv_empty_0028 A B R)

theorem nb089_compact_fv_empty_0029 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_042 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0079 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_042 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_042, fv_syn_c1c] using (nb089_compact_fv_empty_0029 u A B R)

theorem nb089_compact_fv_empty_0030 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_039 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0080 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_039 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_039, fv_syn_c1c] using (nb089_compact_fv_empty_0030 A B R)

theorem nb089_compact_fv_empty_0031 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_040 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0081 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_040 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_040, fv_syn_c1c] using (nb089_compact_fv_empty_0031 u A B R)

theorem nb089_compact_fv_empty_0032 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_037 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0082 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_037 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_037, fv_syn_c1c] using (nb089_compact_fv_empty_0032 A B R)

theorem nb089_compact_fv_empty_0033 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_038 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0083 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_038 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_038, fv_syn_c1c] using (nb089_compact_fv_empty_0033 u A B R)

theorem nb089_compact_envfresh_0003 (u : Var) (A : Class) (B : Class) (R : Class) : TEnvFresh [((nb089_alpha_dummy_023 A B R), (nb089_alpha_dummy_026 u A B R)), ((nb089_alpha_dummy_022 A B R), (nb089_alpha_dummy_025 u A B R)), ((nb089_alpha_dummy_021 A B R), (nb089_alpha_dummy_024 u A B R)), ((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)), ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)), ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)), ((nb089_alpha_dummy_041 A B R), (nb089_alpha_dummy_042 u A B R)), ((nb089_alpha_dummy_039 A B R), (nb089_alpha_dummy_040 u A B R)), ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)), ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)), ((nb089_alpha_dummy_037 A B R), (nb089_alpha_dummy_038 u A B R)), ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb089_alpha_dummy_023 A B R) (nb089_alpha_dummy_026 u A B R) (nb089_wpp_notmem_0000 A B R) (nb089_wpp_notmem_0001 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_022 A B R) (nb089_alpha_dummy_025 u A B R) (nb089_wpp_notmem_0002 A B R) (nb089_wpp_notmem_0003 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_021 A B R) (nb089_alpha_dummy_024 u A B R) (nb089_wpp_notmem_0004 A B R) (nb089_wpp_notmem_0005 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_019 A B R) (nb089_alpha_dummy_020 u A B R) (nb089_wpp_notmem_0006 A B R) (nb089_wpp_notmem_0007 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_015 A B R) (nb089_alpha_dummy_017 u A B R) (nb089_wpp_notmem_0008 A B R) (nb089_wpp_notmem_0009 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_016 A B R) (nb089_alpha_dummy_018 u A B R) (nb089_wpp_notmem_0010 A B R) (nb089_wpp_notmem_0011 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_041 A B R) (nb089_alpha_dummy_042 u A B R) (nb089_wpp_notmem_0078 A B R) (nb089_wpp_notmem_0079 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_039 A B R) (nb089_alpha_dummy_040 u A B R) (nb089_wpp_notmem_0080 A B R) (nb089_wpp_notmem_0081 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_008 A B R) (nb089_alpha_dummy_010 u A B R) (nb089_wpp_notmem_0012 A B R) (nb089_wpp_notmem_0013 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_007 A B R) (nb089_alpha_dummy_009 u A B R) (nb089_wpp_notmem_0014 A B R) (nb089_wpp_notmem_0015 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_037 A B R) (nb089_alpha_dummy_038 u A B R) (nb089_wpp_notmem_0082 A B R) (nb089_wpp_notmem_0083 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_011 A B R) (nb089_alpha_dummy_012 u A B R) (nb089_wpp_notmem_0018 A B R) (nb089_wpp_notmem_0019 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_003 A B R) (nb089_alpha_dummy_004 u A B R) (nb089_wpp_notmem_0020 A B R) (nb089_wpp_notmem_0021 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_000 A B R) u (nb089_wpp_notmem_0022 A B R) (nb089_wpp_notmem_0023 u) (TEnvFresh.consFresh (nb089_alpha_dummy_005 A B R) (nb089_alpha_dummy_006 u A B R) (nb089_wpp_notmem_0024 A B R) (nb089_wpp_notmem_0025 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_001 A B R) (nb089_alpha_dummy_002 u A B R) (nb089_wpp_notmem_0026 A B R) (nb089_wpp_notmem_0027 u A B R) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))

noncomputable def nb089_wpp_refl_0003 (u : Var) (A : Class) (B : Class) (R : Class) : TReflOn [((nb089_alpha_dummy_023 A B R), (nb089_alpha_dummy_026 u A B R)), ((nb089_alpha_dummy_022 A B R), (nb089_alpha_dummy_025 u A B R)), ((nb089_alpha_dummy_021 A B R), (nb089_alpha_dummy_024 u A B R)), ((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)), ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)), ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)), ((nb089_alpha_dummy_041 A B R), (nb089_alpha_dummy_042 u A B R)), ((nb089_alpha_dummy_039 A B R), (nb089_alpha_dummy_040 u A B R)), ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)), ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)), ((nb089_alpha_dummy_037 A B R), (nb089_alpha_dummy_038 u A B R)), ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb089_compact_envfresh_0003 u A B R)

theorem nb089_wpp_notmem_0084 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_041 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_041, fv_syn_c0] using (nb089_compact_fv_empty_0028 A B R)

theorem nb089_wpp_notmem_0085 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_042 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_042, fv_syn_c0] using (nb089_compact_fv_empty_0029 u A B R)

theorem nb089_wpp_notmem_0086 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_039 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_039, fv_syn_c0] using (nb089_compact_fv_empty_0030 A B R)

theorem nb089_wpp_notmem_0087 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_040 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_040, fv_syn_c0] using (nb089_compact_fv_empty_0031 u A B R)

theorem nb089_wpp_notmem_0088 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_037 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_037, fv_syn_c0] using (nb089_compact_fv_empty_0032 A B R)

theorem nb089_wpp_notmem_0089 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_038 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_038, fv_syn_c0] using (nb089_compact_fv_empty_0033 u A B R)

theorem nb089_compact_envfresh_0004 (u : Var) (A : Class) (B : Class) (R : Class) : TEnvFresh [((nb089_alpha_dummy_023 A B R), (nb089_alpha_dummy_026 u A B R)), ((nb089_alpha_dummy_022 A B R), (nb089_alpha_dummy_025 u A B R)), ((nb089_alpha_dummy_021 A B R), (nb089_alpha_dummy_024 u A B R)), ((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)), ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)), ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)), ((nb089_alpha_dummy_041 A B R), (nb089_alpha_dummy_042 u A B R)), ((nb089_alpha_dummy_039 A B R), (nb089_alpha_dummy_040 u A B R)), ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)), ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)), ((nb089_alpha_dummy_037 A B R), (nb089_alpha_dummy_038 u A B R)), ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb089_alpha_dummy_023 A B R) (nb089_alpha_dummy_026 u A B R) (nb089_wpp_notmem_0028 A B R) (nb089_wpp_notmem_0029 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_022 A B R) (nb089_alpha_dummy_025 u A B R) (nb089_wpp_notmem_0030 A B R) (nb089_wpp_notmem_0031 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_021 A B R) (nb089_alpha_dummy_024 u A B R) (nb089_wpp_notmem_0032 A B R) (nb089_wpp_notmem_0033 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_019 A B R) (nb089_alpha_dummy_020 u A B R) (nb089_wpp_notmem_0034 A B R) (nb089_wpp_notmem_0035 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_015 A B R) (nb089_alpha_dummy_017 u A B R) (nb089_wpp_notmem_0036 A B R) (nb089_wpp_notmem_0037 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_016 A B R) (nb089_alpha_dummy_018 u A B R) (nb089_wpp_notmem_0038 A B R) (nb089_wpp_notmem_0039 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_041 A B R) (nb089_alpha_dummy_042 u A B R) (nb089_wpp_notmem_0084 A B R) (nb089_wpp_notmem_0085 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_039 A B R) (nb089_alpha_dummy_040 u A B R) (nb089_wpp_notmem_0086 A B R) (nb089_wpp_notmem_0087 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_008 A B R) (nb089_alpha_dummy_010 u A B R) (nb089_wpp_notmem_0040 A B R) (nb089_wpp_notmem_0041 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_007 A B R) (nb089_alpha_dummy_009 u A B R) (nb089_wpp_notmem_0042 A B R) (nb089_wpp_notmem_0043 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_037 A B R) (nb089_alpha_dummy_038 u A B R) (nb089_wpp_notmem_0088 A B R) (nb089_wpp_notmem_0089 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_011 A B R) (nb089_alpha_dummy_012 u A B R) (nb089_wpp_notmem_0046 A B R) (nb089_wpp_notmem_0047 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_003 A B R) (nb089_alpha_dummy_004 u A B R) (nb089_wpp_notmem_0048 A B R) (nb089_wpp_notmem_0049 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_000 A B R) u (nb089_wpp_notmem_0050 A B R) (nb089_wpp_notmem_0051 u) (TEnvFresh.consFresh (nb089_alpha_dummy_005 A B R) (nb089_alpha_dummy_006 u A B R) (nb089_wpp_notmem_0052 A B R) (nb089_wpp_notmem_0053 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_001 A B R) (nb089_alpha_dummy_002 u A B R) (nb089_wpp_notmem_0054 A B R) (nb089_wpp_notmem_0055 u A B R) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))

noncomputable def nb089_wpp_refl_0004 (u : Var) (A : Class) (B : Class) (R : Class) : TReflOn [((nb089_alpha_dummy_023 A B R), (nb089_alpha_dummy_026 u A B R)), ((nb089_alpha_dummy_022 A B R), (nb089_alpha_dummy_025 u A B R)), ((nb089_alpha_dummy_021 A B R), (nb089_alpha_dummy_024 u A B R)), ((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)), ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)), ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)), ((nb089_alpha_dummy_041 A B R), (nb089_alpha_dummy_042 u A B R)), ((nb089_alpha_dummy_039 A B R), (nb089_alpha_dummy_040 u A B R)), ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)), ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)), ((nb089_alpha_dummy_037 A B R), (nb089_alpha_dummy_038 u A B R)), ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb089_compact_envfresh_0004 u A B R)

theorem nb089_wpp_notmem_0090 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_041 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_041, fv_syn_cnnc] using (nb089_compact_fv_empty_0028 A B R)

theorem nb089_wpp_notmem_0091 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_042 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_042, fv_syn_cnnc] using (nb089_compact_fv_empty_0029 u A B R)

theorem nb089_wpp_notmem_0092 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_039 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_039, fv_syn_cnnc] using (nb089_compact_fv_empty_0030 A B R)

theorem nb089_wpp_notmem_0093 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_040 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_040, fv_syn_cnnc] using (nb089_compact_fv_empty_0031 u A B R)

theorem nb089_wpp_notmem_0094 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_037 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_037, fv_syn_cnnc] using (nb089_compact_fv_empty_0032 A B R)

theorem nb089_wpp_notmem_0095 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_038 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_038, fv_syn_cnnc] using (nb089_compact_fv_empty_0033 u A B R)

theorem nb089_compact_envfresh_0005 (u : Var) (A : Class) (B : Class) (R : Class) : TEnvFresh [((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)), ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)), ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)), ((nb089_alpha_dummy_041 A B R), (nb089_alpha_dummy_042 u A B R)), ((nb089_alpha_dummy_039 A B R), (nb089_alpha_dummy_040 u A B R)), ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)), ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)), ((nb089_alpha_dummy_037 A B R), (nb089_alpha_dummy_038 u A B R)), ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb089_alpha_dummy_019 A B R) (nb089_alpha_dummy_020 u A B R) (nb089_wpp_notmem_0056 A B R) (nb089_wpp_notmem_0057 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_015 A B R) (nb089_alpha_dummy_017 u A B R) (nb089_wpp_notmem_0058 A B R) (nb089_wpp_notmem_0059 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_016 A B R) (nb089_alpha_dummy_018 u A B R) (nb089_wpp_notmem_0060 A B R) (nb089_wpp_notmem_0061 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_041 A B R) (nb089_alpha_dummy_042 u A B R) (nb089_wpp_notmem_0090 A B R) (nb089_wpp_notmem_0091 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_039 A B R) (nb089_alpha_dummy_040 u A B R) (nb089_wpp_notmem_0092 A B R) (nb089_wpp_notmem_0093 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_008 A B R) (nb089_alpha_dummy_010 u A B R) (nb089_wpp_notmem_0062 A B R) (nb089_wpp_notmem_0063 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_007 A B R) (nb089_alpha_dummy_009 u A B R) (nb089_wpp_notmem_0064 A B R) (nb089_wpp_notmem_0065 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_037 A B R) (nb089_alpha_dummy_038 u A B R) (nb089_wpp_notmem_0094 A B R) (nb089_wpp_notmem_0095 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_011 A B R) (nb089_alpha_dummy_012 u A B R) (nb089_wpp_notmem_0068 A B R) (nb089_wpp_notmem_0069 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_003 A B R) (nb089_alpha_dummy_004 u A B R) (nb089_wpp_notmem_0070 A B R) (nb089_wpp_notmem_0071 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_000 A B R) u (nb089_wpp_notmem_0072 A B R) (nb089_wpp_notmem_0073 u) (TEnvFresh.consFresh (nb089_alpha_dummy_005 A B R) (nb089_alpha_dummy_006 u A B R) (nb089_wpp_notmem_0074 A B R) (nb089_wpp_notmem_0075 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_001 A B R) (nb089_alpha_dummy_002 u A B R) (nb089_wpp_notmem_0076 A B R) (nb089_wpp_notmem_0077 u A B R) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))

noncomputable def nb089_wpp_refl_0005 (u : Var) (A : Class) (B : Class) (R : Class) : TReflOn [((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)), ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)), ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)), ((nb089_alpha_dummy_041 A B R), (nb089_alpha_dummy_042 u A B R)), ((nb089_alpha_dummy_039 A B R), (nb089_alpha_dummy_040 u A B R)), ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)), ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)), ((nb089_alpha_dummy_037 A B R), (nb089_alpha_dummy_038 u A B R)), ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb089_compact_envfresh_0005 u A B R)

theorem nb089_wpp_notmem_0096 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_039 A B R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb089_alpha_dummy_039, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb089_compact_fv_empty_0030 A B R)

theorem nb089_wpp_notmem_0097 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_040 u A B R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb089_alpha_dummy_040, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb089_compact_fv_empty_0031 u A B R)

theorem nb089_wpp_notmem_0098 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_008 A B R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb089_alpha_dummy_008, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb089_compact_fv_empty_0012 A B R)

theorem nb089_wpp_notmem_0099 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_010 u A B R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb089_alpha_dummy_010, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb089_compact_fv_empty_0013 u A B R)

theorem nb089_wpp_notmem_0100 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_007 A B R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb089_alpha_dummy_007, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb089_compact_fv_empty_0014 A B R)

theorem nb089_wpp_notmem_0101 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_009 u A B R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb089_alpha_dummy_009, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb089_compact_fv_empty_0015 u A B R)

theorem nb089_wpp_notmem_0102 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_037 A B R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb089_alpha_dummy_037, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb089_compact_fv_empty_0032 A B R)

theorem nb089_wpp_notmem_0103 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_038 u A B R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb089_alpha_dummy_038, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb089_compact_fv_empty_0033 u A B R)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
