import NAR4C083C001Part001

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

theorem nb083_wpp_notmem_0007 (b : Var) (c : Var) : (nb083_alpha_dummy_020 b c) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_020, fv_syn_c1c] using (nb083_compact_fv_empty_0003 b c)

theorem nb083_compact_fv_empty_0004 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_016 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0008 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_016 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_016, fv_syn_c1c] using (nb083_compact_fv_empty_0004 A B C R)

theorem nb083_compact_fv_empty_0005 (b : Var) (c : Var) : (nb083_alpha_dummy_019 b c) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0009 (b : Var) (c : Var) : (nb083_alpha_dummy_019 b c) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_019, fv_syn_c1c] using (nb083_compact_fv_empty_0005 b c)

theorem nb083_compact_fv_empty_0006 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_014 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0010 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_014 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_014, fv_syn_c1c] using (nb083_compact_fv_empty_0006 A B C R)

theorem nb083_compact_fv_empty_0007 (b : Var) (c : Var) : (nb083_alpha_dummy_015 b c) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0011 (b : Var) (c : Var) : (nb083_alpha_dummy_015 b c) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_015, fv_syn_c1c] using (nb083_compact_fv_empty_0007 b c)

theorem nb083_compact_fv_empty_0008 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_010 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0012 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_010 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_010, fv_syn_c1c] using (nb083_compact_fv_empty_0008 A B C R)

theorem nb083_compact_fv_empty_0009 (b : Var) (c : Var) : (nb083_alpha_dummy_012 b c) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0013 (b : Var) (c : Var) : (nb083_alpha_dummy_012 b c) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_012, fv_syn_c1c] using (nb083_compact_fv_empty_0009 b c)

theorem nb083_compact_fv_empty_0010 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_011 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0014 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_011 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_011, fv_syn_c1c] using (nb083_compact_fv_empty_0010 A B C R)

theorem nb083_compact_fv_empty_0011 (b : Var) (c : Var) : (nb083_alpha_dummy_013 b c) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0015 (b : Var) (c : Var) : (nb083_alpha_dummy_013 b c) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_013, fv_syn_c1c] using (nb083_compact_fv_empty_0011 b c)

theorem nb083_compact_fv_empty_0012 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_003 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0016 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_003 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_003, fv_syn_c1c] using (nb083_compact_fv_empty_0012 A B C R)

theorem nb083_compact_fv_empty_0013 (b : Var) (c : Var) : (nb083_alpha_dummy_005 b c) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0017 (b : Var) (c : Var) : (nb083_alpha_dummy_005 b c) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_005, fv_syn_c1c] using (nb083_compact_fv_empty_0013 b c)

theorem nb083_compact_fv_empty_0014 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_002 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0018 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_002 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_002, fv_syn_c1c] using (nb083_compact_fv_empty_0014 A B C R)

theorem nb083_compact_fv_empty_0015 (b : Var) (c : Var) : (nb083_alpha_dummy_004 b c) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0019 (b : Var) (c : Var) : (nb083_alpha_dummy_004 b c) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_004, fv_syn_c1c] using (nb083_compact_fv_empty_0015 b c)

theorem nb083_compact_fv_empty_0016 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_008 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0020 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_008 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_008, fv_syn_c1c] using (nb083_compact_fv_empty_0016 A B C R)

theorem nb083_compact_fv_empty_0017 (b : Var) (c : Var) : (nb083_alpha_dummy_009 b c) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0021 (b : Var) (c : Var) : (nb083_alpha_dummy_009 b c) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_009, fv_syn_c1c] using (nb083_compact_fv_empty_0017 b c)

theorem nb083_compact_fv_empty_0018 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_006 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0022 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_006 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_006, fv_syn_c1c] using (nb083_compact_fv_empty_0018 A B C R)

theorem nb083_compact_fv_empty_0019 (b : Var) (c : Var) : (nb083_alpha_dummy_007 b c) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0023 (b : Var) (c : Var) : (nb083_alpha_dummy_007 b c) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_007, fv_syn_c1c] using (nb083_compact_fv_empty_0019 b c)

theorem nb083_compact_fv_empty_0020 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_001 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0024 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_001 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_001, fv_syn_c1c] using (nb083_compact_fv_empty_0020 A B C R)

theorem nb083_compact_fv_empty_0021 (c : Var) : c ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0025 (c : Var) : c ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb083_compact_fv_empty_0021 c)

theorem nb083_compact_fv_empty_0022 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_000 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0026 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_000 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_000, fv_syn_c1c] using (nb083_compact_fv_empty_0022 A B C R)

theorem nb083_compact_fv_empty_0023 (b : Var) : b ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0027 (b : Var) : b ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb083_compact_fv_empty_0023 b)

theorem nb083_compact_envfresh_0004 (A : Class) (B : Class) (C : Class) (R : Class) (b : Var) (c : Var) : TEnvFresh [((nb083_alpha_dummy_018 A B C R), (nb083_alpha_dummy_021 b c)), ((nb083_alpha_dummy_017 A B C R), (nb083_alpha_dummy_020 b c)), ((nb083_alpha_dummy_016 A B C R), (nb083_alpha_dummy_019 b c)), ((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015 b c)), ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)), ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)), ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)), ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)), ((nb083_alpha_dummy_008 A B C R), (nb083_alpha_dummy_009 b c)), ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)), ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb083_alpha_dummy_018 A B C R) (nb083_alpha_dummy_021 b c) (nb083_wpp_notmem_0004 A B C R) (nb083_wpp_notmem_0005 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_017 A B C R) (nb083_alpha_dummy_020 b c) (nb083_wpp_notmem_0006 A B C R) (nb083_wpp_notmem_0007 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_016 A B C R) (nb083_alpha_dummy_019 b c) (nb083_wpp_notmem_0008 A B C R) (nb083_wpp_notmem_0009 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_014 A B C R) (nb083_alpha_dummy_015 b c) (nb083_wpp_notmem_0010 A B C R) (nb083_wpp_notmem_0011 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_010 A B C R) (nb083_alpha_dummy_012 b c) (nb083_wpp_notmem_0012 A B C R) (nb083_wpp_notmem_0013 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_011 A B C R) (nb083_alpha_dummy_013 b c) (nb083_wpp_notmem_0014 A B C R) (nb083_wpp_notmem_0015 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_003 A B C R) (nb083_alpha_dummy_005 b c) (nb083_wpp_notmem_0016 A B C R) (nb083_wpp_notmem_0017 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_002 A B C R) (nb083_alpha_dummy_004 b c) (nb083_wpp_notmem_0018 A B C R) (nb083_wpp_notmem_0019 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_008 A B C R) (nb083_alpha_dummy_009 b c) (nb083_wpp_notmem_0020 A B C R) (nb083_wpp_notmem_0021 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_006 A B C R) (nb083_alpha_dummy_007 b c) (nb083_wpp_notmem_0022 A B C R) (nb083_wpp_notmem_0023 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_001 A B C R) c (nb083_wpp_notmem_0024 A B C R) (nb083_wpp_notmem_0025 c) (TEnvFresh.consFresh (nb083_alpha_dummy_000 A B C R) b (nb083_wpp_notmem_0026 A B C R) (nb083_wpp_notmem_0027 b) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))

noncomputable def nb083_wpp_refl_0002 (A : Class) (B : Class) (C : Class) (R : Class) (b : Var) (c : Var) : TReflOn [((nb083_alpha_dummy_018 A B C R), (nb083_alpha_dummy_021 b c)), ((nb083_alpha_dummy_017 A B C R), (nb083_alpha_dummy_020 b c)), ((nb083_alpha_dummy_016 A B C R), (nb083_alpha_dummy_019 b c)), ((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015 b c)), ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)), ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)), ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)), ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)), ((nb083_alpha_dummy_008 A B C R), (nb083_alpha_dummy_009 b c)), ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)), ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb083_compact_envfresh_0004 A B C R b c)

theorem nb083_wpp_notmem_0028 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_018 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_018, fv_syn_c0] using (nb083_compact_fv_empty_0000 A B C R)

theorem nb083_wpp_notmem_0029 (b : Var) (c : Var) : (nb083_alpha_dummy_021 b c) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_021, fv_syn_c0] using (nb083_compact_fv_empty_0001 b c)

theorem nb083_wpp_notmem_0030 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_017 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_017, fv_syn_c0] using (nb083_compact_fv_empty_0002 A B C R)

theorem nb083_wpp_notmem_0031 (b : Var) (c : Var) : (nb083_alpha_dummy_020 b c) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_020, fv_syn_c0] using (nb083_compact_fv_empty_0003 b c)

theorem nb083_wpp_notmem_0032 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_016 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_016, fv_syn_c0] using (nb083_compact_fv_empty_0004 A B C R)

theorem nb083_wpp_notmem_0033 (b : Var) (c : Var) : (nb083_alpha_dummy_019 b c) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_019, fv_syn_c0] using (nb083_compact_fv_empty_0005 b c)

theorem nb083_wpp_notmem_0034 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_014 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_014, fv_syn_c0] using (nb083_compact_fv_empty_0006 A B C R)

theorem nb083_wpp_notmem_0035 (b : Var) (c : Var) : (nb083_alpha_dummy_015 b c) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_015, fv_syn_c0] using (nb083_compact_fv_empty_0007 b c)

theorem nb083_wpp_notmem_0036 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_010 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_010, fv_syn_c0] using (nb083_compact_fv_empty_0008 A B C R)

theorem nb083_wpp_notmem_0037 (b : Var) (c : Var) : (nb083_alpha_dummy_012 b c) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_012, fv_syn_c0] using (nb083_compact_fv_empty_0009 b c)

theorem nb083_wpp_notmem_0038 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_011 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_011, fv_syn_c0] using (nb083_compact_fv_empty_0010 A B C R)

theorem nb083_wpp_notmem_0039 (b : Var) (c : Var) : (nb083_alpha_dummy_013 b c) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_013, fv_syn_c0] using (nb083_compact_fv_empty_0011 b c)

theorem nb083_wpp_notmem_0040 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_003 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_003, fv_syn_c0] using (nb083_compact_fv_empty_0012 A B C R)

theorem nb083_wpp_notmem_0041 (b : Var) (c : Var) : (nb083_alpha_dummy_005 b c) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_005, fv_syn_c0] using (nb083_compact_fv_empty_0013 b c)

theorem nb083_wpp_notmem_0042 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_002 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_002, fv_syn_c0] using (nb083_compact_fv_empty_0014 A B C R)

theorem nb083_wpp_notmem_0043 (b : Var) (c : Var) : (nb083_alpha_dummy_004 b c) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_004, fv_syn_c0] using (nb083_compact_fv_empty_0015 b c)

theorem nb083_wpp_notmem_0044 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_008 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_008, fv_syn_c0] using (nb083_compact_fv_empty_0016 A B C R)

theorem nb083_wpp_notmem_0045 (b : Var) (c : Var) : (nb083_alpha_dummy_009 b c) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_009, fv_syn_c0] using (nb083_compact_fv_empty_0017 b c)

theorem nb083_wpp_notmem_0046 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_006 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_006, fv_syn_c0] using (nb083_compact_fv_empty_0018 A B C R)

theorem nb083_wpp_notmem_0047 (b : Var) (c : Var) : (nb083_alpha_dummy_007 b c) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_007, fv_syn_c0] using (nb083_compact_fv_empty_0019 b c)

theorem nb083_wpp_notmem_0048 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_001 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_001, fv_syn_c0] using (nb083_compact_fv_empty_0020 A B C R)

theorem nb083_wpp_notmem_0049 (c : Var) : c ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb083_compact_fv_empty_0021 c)

theorem nb083_wpp_notmem_0050 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_000 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_000, fv_syn_c0] using (nb083_compact_fv_empty_0022 A B C R)

theorem nb083_wpp_notmem_0051 (b : Var) : b ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb083_compact_fv_empty_0023 b)

theorem nb083_compact_envfresh_0005 (A : Class) (B : Class) (C : Class) (R : Class) (b : Var) (c : Var) : TEnvFresh [((nb083_alpha_dummy_018 A B C R), (nb083_alpha_dummy_021 b c)), ((nb083_alpha_dummy_017 A B C R), (nb083_alpha_dummy_020 b c)), ((nb083_alpha_dummy_016 A B C R), (nb083_alpha_dummy_019 b c)), ((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015 b c)), ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)), ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)), ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)), ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)), ((nb083_alpha_dummy_008 A B C R), (nb083_alpha_dummy_009 b c)), ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)), ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb083_alpha_dummy_018 A B C R) (nb083_alpha_dummy_021 b c) (nb083_wpp_notmem_0028 A B C R) (nb083_wpp_notmem_0029 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_017 A B C R) (nb083_alpha_dummy_020 b c) (nb083_wpp_notmem_0030 A B C R) (nb083_wpp_notmem_0031 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_016 A B C R) (nb083_alpha_dummy_019 b c) (nb083_wpp_notmem_0032 A B C R) (nb083_wpp_notmem_0033 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_014 A B C R) (nb083_alpha_dummy_015 b c) (nb083_wpp_notmem_0034 A B C R) (nb083_wpp_notmem_0035 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_010 A B C R) (nb083_alpha_dummy_012 b c) (nb083_wpp_notmem_0036 A B C R) (nb083_wpp_notmem_0037 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_011 A B C R) (nb083_alpha_dummy_013 b c) (nb083_wpp_notmem_0038 A B C R) (nb083_wpp_notmem_0039 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_003 A B C R) (nb083_alpha_dummy_005 b c) (nb083_wpp_notmem_0040 A B C R) (nb083_wpp_notmem_0041 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_002 A B C R) (nb083_alpha_dummy_004 b c) (nb083_wpp_notmem_0042 A B C R) (nb083_wpp_notmem_0043 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_008 A B C R) (nb083_alpha_dummy_009 b c) (nb083_wpp_notmem_0044 A B C R) (nb083_wpp_notmem_0045 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_006 A B C R) (nb083_alpha_dummy_007 b c) (nb083_wpp_notmem_0046 A B C R) (nb083_wpp_notmem_0047 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_001 A B C R) c (nb083_wpp_notmem_0048 A B C R) (nb083_wpp_notmem_0049 c) (TEnvFresh.consFresh (nb083_alpha_dummy_000 A B C R) b (nb083_wpp_notmem_0050 A B C R) (nb083_wpp_notmem_0051 b) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))

noncomputable def nb083_wpp_refl_0003 (A : Class) (B : Class) (C : Class) (R : Class) (b : Var) (c : Var) : TReflOn [((nb083_alpha_dummy_018 A B C R), (nb083_alpha_dummy_021 b c)), ((nb083_alpha_dummy_017 A B C R), (nb083_alpha_dummy_020 b c)), ((nb083_alpha_dummy_016 A B C R), (nb083_alpha_dummy_019 b c)), ((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015 b c)), ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)), ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)), ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)), ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)), ((nb083_alpha_dummy_008 A B C R), (nb083_alpha_dummy_009 b c)), ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)), ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb083_compact_envfresh_0005 A B C R b c)

theorem nb083_wpp_notmem_0052 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_014 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb083_alpha_dummy_014, fv_syn_cnnc] using (nb083_compact_fv_empty_0006 A B C R)

theorem nb083_wpp_notmem_0053 (b : Var) (c : Var) : (nb083_alpha_dummy_015 b c) ∉ ((syn_cnnc)).fv := by
  simpa only [nb083_alpha_dummy_015, fv_syn_cnnc] using (nb083_compact_fv_empty_0007 b c)

theorem nb083_wpp_notmem_0054 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_010 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb083_alpha_dummy_010, fv_syn_cnnc] using (nb083_compact_fv_empty_0008 A B C R)

theorem nb083_wpp_notmem_0055 (b : Var) (c : Var) : (nb083_alpha_dummy_012 b c) ∉ ((syn_cnnc)).fv := by
  simpa only [nb083_alpha_dummy_012, fv_syn_cnnc] using (nb083_compact_fv_empty_0009 b c)

theorem nb083_wpp_notmem_0056 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_011 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb083_alpha_dummy_011, fv_syn_cnnc] using (nb083_compact_fv_empty_0010 A B C R)

theorem nb083_wpp_notmem_0057 (b : Var) (c : Var) : (nb083_alpha_dummy_013 b c) ∉ ((syn_cnnc)).fv := by
  simpa only [nb083_alpha_dummy_013, fv_syn_cnnc] using (nb083_compact_fv_empty_0011 b c)

theorem nb083_wpp_notmem_0058 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_003 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb083_alpha_dummy_003, fv_syn_cnnc] using (nb083_compact_fv_empty_0012 A B C R)

theorem nb083_wpp_notmem_0059 (b : Var) (c : Var) : (nb083_alpha_dummy_005 b c) ∉ ((syn_cnnc)).fv := by
  simpa only [nb083_alpha_dummy_005, fv_syn_cnnc] using (nb083_compact_fv_empty_0013 b c)

theorem nb083_wpp_notmem_0060 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_002 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb083_alpha_dummy_002, fv_syn_cnnc] using (nb083_compact_fv_empty_0014 A B C R)

theorem nb083_wpp_notmem_0061 (b : Var) (c : Var) : (nb083_alpha_dummy_004 b c) ∉ ((syn_cnnc)).fv := by
  simpa only [nb083_alpha_dummy_004, fv_syn_cnnc] using (nb083_compact_fv_empty_0015 b c)

theorem nb083_wpp_notmem_0062 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_008 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb083_alpha_dummy_008, fv_syn_cnnc] using (nb083_compact_fv_empty_0016 A B C R)

theorem nb083_wpp_notmem_0063 (b : Var) (c : Var) : (nb083_alpha_dummy_009 b c) ∉ ((syn_cnnc)).fv := by
  simpa only [nb083_alpha_dummy_009, fv_syn_cnnc] using (nb083_compact_fv_empty_0017 b c)

theorem nb083_wpp_notmem_0064 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_006 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb083_alpha_dummy_006, fv_syn_cnnc] using (nb083_compact_fv_empty_0018 A B C R)

theorem nb083_wpp_notmem_0065 (b : Var) (c : Var) : (nb083_alpha_dummy_007 b c) ∉ ((syn_cnnc)).fv := by
  simpa only [nb083_alpha_dummy_007, fv_syn_cnnc] using (nb083_compact_fv_empty_0019 b c)

theorem nb083_wpp_notmem_0066 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_001 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb083_alpha_dummy_001, fv_syn_cnnc] using (nb083_compact_fv_empty_0020 A B C R)

theorem nb083_wpp_notmem_0067 (c : Var) : c ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb083_compact_fv_empty_0021 c)

theorem nb083_wpp_notmem_0068 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_000 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb083_alpha_dummy_000, fv_syn_cnnc] using (nb083_compact_fv_empty_0022 A B C R)

theorem nb083_wpp_notmem_0069 (b : Var) : b ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb083_compact_fv_empty_0023 b)

theorem nb083_compact_envfresh_0006 (A : Class) (B : Class) (C : Class) (R : Class) (b : Var) (c : Var) : TEnvFresh [((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015 b c)), ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)), ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)), ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)), ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)), ((nb083_alpha_dummy_008 A B C R), (nb083_alpha_dummy_009 b c)), ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)), ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb083_alpha_dummy_014 A B C R) (nb083_alpha_dummy_015 b c) (nb083_wpp_notmem_0052 A B C R) (nb083_wpp_notmem_0053 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_010 A B C R) (nb083_alpha_dummy_012 b c) (nb083_wpp_notmem_0054 A B C R) (nb083_wpp_notmem_0055 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_011 A B C R) (nb083_alpha_dummy_013 b c) (nb083_wpp_notmem_0056 A B C R) (nb083_wpp_notmem_0057 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_003 A B C R) (nb083_alpha_dummy_005 b c) (nb083_wpp_notmem_0058 A B C R) (nb083_wpp_notmem_0059 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_002 A B C R) (nb083_alpha_dummy_004 b c) (nb083_wpp_notmem_0060 A B C R) (nb083_wpp_notmem_0061 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_008 A B C R) (nb083_alpha_dummy_009 b c) (nb083_wpp_notmem_0062 A B C R) (nb083_wpp_notmem_0063 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_006 A B C R) (nb083_alpha_dummy_007 b c) (nb083_wpp_notmem_0064 A B C R) (nb083_wpp_notmem_0065 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_001 A B C R) c (nb083_wpp_notmem_0066 A B C R) (nb083_wpp_notmem_0067 c) (TEnvFresh.consFresh (nb083_alpha_dummy_000 A B C R) b (nb083_wpp_notmem_0068 A B C R) (nb083_wpp_notmem_0069 b) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))

noncomputable def nb083_wpp_refl_0004 (A : Class) (B : Class) (C : Class) (R : Class) (b : Var) (c : Var) : TReflOn [((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015 b c)), ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)), ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)), ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)), ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)), ((nb083_alpha_dummy_008 A B C R), (nb083_alpha_dummy_009 b c)), ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)), ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb083_compact_envfresh_0006 A B C R b c)

theorem nb083_compact_fv_empty_0024 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_036 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0070 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_036 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_036, fv_syn_c1c] using (nb083_compact_fv_empty_0024 A B C R)

theorem nb083_compact_fv_empty_0025 (b : Var) (c : Var) : (nb083_alpha_dummy_037 b c) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0071 (b : Var) (c : Var) : (nb083_alpha_dummy_037 b c) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_037, fv_syn_c1c] using (nb083_compact_fv_empty_0025 b c)

theorem nb083_compact_fv_empty_0026 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_034 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0072 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_034 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_034, fv_syn_c1c] using (nb083_compact_fv_empty_0026 A B C R)

theorem nb083_compact_fv_empty_0027 (b : Var) (c : Var) : (nb083_alpha_dummy_035 b c) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0073 (b : Var) (c : Var) : (nb083_alpha_dummy_035 b c) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_035, fv_syn_c1c] using (nb083_compact_fv_empty_0027 b c)

theorem nb083_compact_fv_empty_0028 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_032 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0074 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_032 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_032, fv_syn_c1c] using (nb083_compact_fv_empty_0028 A B C R)

theorem nb083_compact_fv_empty_0029 (b : Var) (c : Var) : (nb083_alpha_dummy_033 b c) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb083_wpp_notmem_0075 (b : Var) (c : Var) : (nb083_alpha_dummy_033 b c) ∉ ((syn_c1c)).fv := by
  simpa only [nb083_alpha_dummy_033, fv_syn_c1c] using (nb083_compact_fv_empty_0029 b c)

theorem nb083_compact_envfresh_0007 (A : Class) (B : Class) (C : Class) (R : Class) (b : Var) (c : Var) : TEnvFresh [((nb083_alpha_dummy_018 A B C R), (nb083_alpha_dummy_021 b c)), ((nb083_alpha_dummy_017 A B C R), (nb083_alpha_dummy_020 b c)), ((nb083_alpha_dummy_016 A B C R), (nb083_alpha_dummy_019 b c)), ((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015 b c)), ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)), ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)), ((nb083_alpha_dummy_036 A B C R), (nb083_alpha_dummy_037 b c)), ((nb083_alpha_dummy_034 A B C R), (nb083_alpha_dummy_035 b c)), ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)), ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)), ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)), ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)), ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb083_alpha_dummy_018 A B C R) (nb083_alpha_dummy_021 b c) (nb083_wpp_notmem_0004 A B C R) (nb083_wpp_notmem_0005 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_017 A B C R) (nb083_alpha_dummy_020 b c) (nb083_wpp_notmem_0006 A B C R) (nb083_wpp_notmem_0007 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_016 A B C R) (nb083_alpha_dummy_019 b c) (nb083_wpp_notmem_0008 A B C R) (nb083_wpp_notmem_0009 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_014 A B C R) (nb083_alpha_dummy_015 b c) (nb083_wpp_notmem_0010 A B C R) (nb083_wpp_notmem_0011 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_010 A B C R) (nb083_alpha_dummy_012 b c) (nb083_wpp_notmem_0012 A B C R) (nb083_wpp_notmem_0013 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_011 A B C R) (nb083_alpha_dummy_013 b c) (nb083_wpp_notmem_0014 A B C R) (nb083_wpp_notmem_0015 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_036 A B C R) (nb083_alpha_dummy_037 b c) (nb083_wpp_notmem_0070 A B C R) (nb083_wpp_notmem_0071 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_034 A B C R) (nb083_alpha_dummy_035 b c) (nb083_wpp_notmem_0072 A B C R) (nb083_wpp_notmem_0073 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_003 A B C R) (nb083_alpha_dummy_005 b c) (nb083_wpp_notmem_0016 A B C R) (nb083_wpp_notmem_0017 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_002 A B C R) (nb083_alpha_dummy_004 b c) (nb083_wpp_notmem_0018 A B C R) (nb083_wpp_notmem_0019 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_032 A B C R) (nb083_alpha_dummy_033 b c) (nb083_wpp_notmem_0074 A B C R) (nb083_wpp_notmem_0075 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_006 A B C R) (nb083_alpha_dummy_007 b c) (nb083_wpp_notmem_0022 A B C R) (nb083_wpp_notmem_0023 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_001 A B C R) c (nb083_wpp_notmem_0024 A B C R) (nb083_wpp_notmem_0025 c) (TEnvFresh.consFresh (nb083_alpha_dummy_000 A B C R) b (nb083_wpp_notmem_0026 A B C R) (nb083_wpp_notmem_0027 b) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))

noncomputable def nb083_wpp_refl_0005 (A : Class) (B : Class) (C : Class) (R : Class) (b : Var) (c : Var) : TReflOn [((nb083_alpha_dummy_018 A B C R), (nb083_alpha_dummy_021 b c)), ((nb083_alpha_dummy_017 A B C R), (nb083_alpha_dummy_020 b c)), ((nb083_alpha_dummy_016 A B C R), (nb083_alpha_dummy_019 b c)), ((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015 b c)), ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)), ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)), ((nb083_alpha_dummy_036 A B C R), (nb083_alpha_dummy_037 b c)), ((nb083_alpha_dummy_034 A B C R), (nb083_alpha_dummy_035 b c)), ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)), ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)), ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)), ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)), ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb083_compact_envfresh_0007 A B C R b c)

theorem nb083_wpp_notmem_0076 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_036 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_036, fv_syn_c0] using (nb083_compact_fv_empty_0024 A B C R)

theorem nb083_wpp_notmem_0077 (b : Var) (c : Var) : (nb083_alpha_dummy_037 b c) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_037, fv_syn_c0] using (nb083_compact_fv_empty_0025 b c)

theorem nb083_wpp_notmem_0078 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_034 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_034, fv_syn_c0] using (nb083_compact_fv_empty_0026 A B C R)

theorem nb083_wpp_notmem_0079 (b : Var) (c : Var) : (nb083_alpha_dummy_035 b c) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_035, fv_syn_c0] using (nb083_compact_fv_empty_0027 b c)

theorem nb083_wpp_notmem_0080 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_032 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_032, fv_syn_c0] using (nb083_compact_fv_empty_0028 A B C R)

theorem nb083_wpp_notmem_0081 (b : Var) (c : Var) : (nb083_alpha_dummy_033 b c) ∉ ((syn_c0)).fv := by
  simpa only [nb083_alpha_dummy_033, fv_syn_c0] using (nb083_compact_fv_empty_0029 b c)

theorem nb083_compact_envfresh_0008 (A : Class) (B : Class) (C : Class) (R : Class) (b : Var) (c : Var) : TEnvFresh [((nb083_alpha_dummy_018 A B C R), (nb083_alpha_dummy_021 b c)), ((nb083_alpha_dummy_017 A B C R), (nb083_alpha_dummy_020 b c)), ((nb083_alpha_dummy_016 A B C R), (nb083_alpha_dummy_019 b c)), ((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015 b c)), ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)), ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)), ((nb083_alpha_dummy_036 A B C R), (nb083_alpha_dummy_037 b c)), ((nb083_alpha_dummy_034 A B C R), (nb083_alpha_dummy_035 b c)), ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)), ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)), ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)), ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)), ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb083_alpha_dummy_018 A B C R) (nb083_alpha_dummy_021 b c) (nb083_wpp_notmem_0028 A B C R) (nb083_wpp_notmem_0029 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_017 A B C R) (nb083_alpha_dummy_020 b c) (nb083_wpp_notmem_0030 A B C R) (nb083_wpp_notmem_0031 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_016 A B C R) (nb083_alpha_dummy_019 b c) (nb083_wpp_notmem_0032 A B C R) (nb083_wpp_notmem_0033 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_014 A B C R) (nb083_alpha_dummy_015 b c) (nb083_wpp_notmem_0034 A B C R) (nb083_wpp_notmem_0035 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_010 A B C R) (nb083_alpha_dummy_012 b c) (nb083_wpp_notmem_0036 A B C R) (nb083_wpp_notmem_0037 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_011 A B C R) (nb083_alpha_dummy_013 b c) (nb083_wpp_notmem_0038 A B C R) (nb083_wpp_notmem_0039 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_036 A B C R) (nb083_alpha_dummy_037 b c) (nb083_wpp_notmem_0076 A B C R) (nb083_wpp_notmem_0077 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_034 A B C R) (nb083_alpha_dummy_035 b c) (nb083_wpp_notmem_0078 A B C R) (nb083_wpp_notmem_0079 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_003 A B C R) (nb083_alpha_dummy_005 b c) (nb083_wpp_notmem_0040 A B C R) (nb083_wpp_notmem_0041 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_002 A B C R) (nb083_alpha_dummy_004 b c) (nb083_wpp_notmem_0042 A B C R) (nb083_wpp_notmem_0043 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_032 A B C R) (nb083_alpha_dummy_033 b c) (nb083_wpp_notmem_0080 A B C R) (nb083_wpp_notmem_0081 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_006 A B C R) (nb083_alpha_dummy_007 b c) (nb083_wpp_notmem_0046 A B C R) (nb083_wpp_notmem_0047 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_001 A B C R) c (nb083_wpp_notmem_0048 A B C R) (nb083_wpp_notmem_0049 c) (TEnvFresh.consFresh (nb083_alpha_dummy_000 A B C R) b (nb083_wpp_notmem_0050 A B C R) (nb083_wpp_notmem_0051 b) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))

noncomputable def nb083_wpp_refl_0006 (A : Class) (B : Class) (C : Class) (R : Class) (b : Var) (c : Var) : TReflOn [((nb083_alpha_dummy_018 A B C R), (nb083_alpha_dummy_021 b c)), ((nb083_alpha_dummy_017 A B C R), (nb083_alpha_dummy_020 b c)), ((nb083_alpha_dummy_016 A B C R), (nb083_alpha_dummy_019 b c)), ((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015 b c)), ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)), ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)), ((nb083_alpha_dummy_036 A B C R), (nb083_alpha_dummy_037 b c)), ((nb083_alpha_dummy_034 A B C R), (nb083_alpha_dummy_035 b c)), ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)), ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)), ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)), ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)), ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb083_compact_envfresh_0008 A B C R b c)

theorem nb083_wpp_notmem_0082 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_036 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb083_alpha_dummy_036, fv_syn_cnnc] using (nb083_compact_fv_empty_0024 A B C R)

theorem nb083_wpp_notmem_0083 (b : Var) (c : Var) : (nb083_alpha_dummy_037 b c) ∉ ((syn_cnnc)).fv := by
  simpa only [nb083_alpha_dummy_037, fv_syn_cnnc] using (nb083_compact_fv_empty_0025 b c)

theorem nb083_wpp_notmem_0084 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_034 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb083_alpha_dummy_034, fv_syn_cnnc] using (nb083_compact_fv_empty_0026 A B C R)

theorem nb083_wpp_notmem_0085 (b : Var) (c : Var) : (nb083_alpha_dummy_035 b c) ∉ ((syn_cnnc)).fv := by
  simpa only [nb083_alpha_dummy_035, fv_syn_cnnc] using (nb083_compact_fv_empty_0027 b c)

theorem nb083_wpp_notmem_0086 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_032 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb083_alpha_dummy_032, fv_syn_cnnc] using (nb083_compact_fv_empty_0028 A B C R)

theorem nb083_wpp_notmem_0087 (b : Var) (c : Var) : (nb083_alpha_dummy_033 b c) ∉ ((syn_cnnc)).fv := by
  simpa only [nb083_alpha_dummy_033, fv_syn_cnnc] using (nb083_compact_fv_empty_0029 b c)

theorem nb083_compact_envfresh_0009 (A : Class) (B : Class) (C : Class) (R : Class) (b : Var) (c : Var) : TEnvFresh [((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015 b c)), ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)), ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)), ((nb083_alpha_dummy_036 A B C R), (nb083_alpha_dummy_037 b c)), ((nb083_alpha_dummy_034 A B C R), (nb083_alpha_dummy_035 b c)), ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)), ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)), ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)), ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)), ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb083_alpha_dummy_014 A B C R) (nb083_alpha_dummy_015 b c) (nb083_wpp_notmem_0052 A B C R) (nb083_wpp_notmem_0053 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_010 A B C R) (nb083_alpha_dummy_012 b c) (nb083_wpp_notmem_0054 A B C R) (nb083_wpp_notmem_0055 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_011 A B C R) (nb083_alpha_dummy_013 b c) (nb083_wpp_notmem_0056 A B C R) (nb083_wpp_notmem_0057 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_036 A B C R) (nb083_alpha_dummy_037 b c) (nb083_wpp_notmem_0082 A B C R) (nb083_wpp_notmem_0083 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_034 A B C R) (nb083_alpha_dummy_035 b c) (nb083_wpp_notmem_0084 A B C R) (nb083_wpp_notmem_0085 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_003 A B C R) (nb083_alpha_dummy_005 b c) (nb083_wpp_notmem_0058 A B C R) (nb083_wpp_notmem_0059 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_002 A B C R) (nb083_alpha_dummy_004 b c) (nb083_wpp_notmem_0060 A B C R) (nb083_wpp_notmem_0061 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_032 A B C R) (nb083_alpha_dummy_033 b c) (nb083_wpp_notmem_0086 A B C R) (nb083_wpp_notmem_0087 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_006 A B C R) (nb083_alpha_dummy_007 b c) (nb083_wpp_notmem_0064 A B C R) (nb083_wpp_notmem_0065 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_001 A B C R) c (nb083_wpp_notmem_0066 A B C R) (nb083_wpp_notmem_0067 c) (TEnvFresh.consFresh (nb083_alpha_dummy_000 A B C R) b (nb083_wpp_notmem_0068 A B C R) (nb083_wpp_notmem_0069 b) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))

noncomputable def nb083_wpp_refl_0007 (A : Class) (B : Class) (C : Class) (R : Class) (b : Var) (c : Var) : TReflOn [((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015 b c)), ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)), ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)), ((nb083_alpha_dummy_036 A B C R), (nb083_alpha_dummy_037 b c)), ((nb083_alpha_dummy_034 A B C R), (nb083_alpha_dummy_035 b c)), ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)), ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)), ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)), ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)), ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb083_compact_envfresh_0009 A B C R b c)

theorem nb083_wpp_notmem_0088 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_034 A B C R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb083_alpha_dummy_034, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb083_compact_fv_empty_0026 A B C R)

theorem nb083_wpp_notmem_0089 (b : Var) (c : Var) : (nb083_alpha_dummy_035 b c) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb083_alpha_dummy_035, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb083_compact_fv_empty_0027 b c)

theorem nb083_wpp_notmem_0090 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_003 A B C R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb083_alpha_dummy_003, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb083_compact_fv_empty_0012 A B C R)

theorem nb083_wpp_notmem_0091 (b : Var) (c : Var) : (nb083_alpha_dummy_005 b c) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb083_alpha_dummy_005, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb083_compact_fv_empty_0013 b c)

theorem nb083_wpp_notmem_0092 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_002 A B C R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb083_alpha_dummy_002, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb083_compact_fv_empty_0014 A B C R)

theorem nb083_wpp_notmem_0093 (b : Var) (c : Var) : (nb083_alpha_dummy_004 b c) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb083_alpha_dummy_004, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb083_compact_fv_empty_0015 b c)

theorem nb083_wpp_notmem_0094 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_032 A B C R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb083_alpha_dummy_032, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb083_compact_fv_empty_0028 A B C R)

theorem nb083_wpp_notmem_0095 (b : Var) (c : Var) : (nb083_alpha_dummy_033 b c) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb083_alpha_dummy_033, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb083_compact_fv_empty_0029 b c)

theorem nb083_wpp_notmem_0096 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_006 A B C R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb083_alpha_dummy_006, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb083_compact_fv_empty_0018 A B C R)

theorem nb083_wpp_notmem_0097 (b : Var) (c : Var) : (nb083_alpha_dummy_007 b c) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb083_alpha_dummy_007, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb083_compact_fv_empty_0019 b c)

theorem nb083_wpp_notmem_0098 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_001 A B C R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb083_alpha_dummy_001, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb083_compact_fv_empty_0020 A B C R)

theorem nb083_wpp_notmem_0099 (c : Var) : c ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb083_compact_fv_empty_0021 c)

theorem nb083_wpp_notmem_0100 (A : Class) (B : Class) (C : Class) (R : Class) : (nb083_alpha_dummy_000 A B C R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb083_alpha_dummy_000, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb083_compact_fv_empty_0022 A B C R)

theorem nb083_wpp_notmem_0101 (b : Var) : b ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb083_compact_fv_empty_0023 b)

theorem nb083_compact_envfresh_0010 (A : Class) (B : Class) (C : Class) (R : Class) (b : Var) (c : Var) : TEnvFresh [((nb083_alpha_dummy_034 A B C R), (nb083_alpha_dummy_035 b c)), ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)), ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)), ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)), ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)), ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb083_alpha_dummy_034 A B C R) (nb083_alpha_dummy_035 b c) (nb083_wpp_notmem_0088 A B C R) (nb083_wpp_notmem_0089 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_003 A B C R) (nb083_alpha_dummy_005 b c) (nb083_wpp_notmem_0090 A B C R) (nb083_wpp_notmem_0091 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_002 A B C R) (nb083_alpha_dummy_004 b c) (nb083_wpp_notmem_0092 A B C R) (nb083_wpp_notmem_0093 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_032 A B C R) (nb083_alpha_dummy_033 b c) (nb083_wpp_notmem_0094 A B C R) (nb083_wpp_notmem_0095 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_006 A B C R) (nb083_alpha_dummy_007 b c) (nb083_wpp_notmem_0096 A B C R) (nb083_wpp_notmem_0097 b c) (TEnvFresh.consFresh (nb083_alpha_dummy_001 A B C R) c (nb083_wpp_notmem_0098 A B C R) (nb083_wpp_notmem_0099 c) (TEnvFresh.consFresh (nb083_alpha_dummy_000 A B C R) b (nb083_wpp_notmem_0100 A B C R) (nb083_wpp_notmem_0101 b) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))

noncomputable def nb083_wpp_refl_0008 (A : Class) (B : Class) (C : Class) (R : Class) (b : Var) (c : Var) : TReflOn [((nb083_alpha_dummy_034 A B C R), (nb083_alpha_dummy_035 b c)), ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)), ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)), ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)), ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)), ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb083_compact_envfresh_0010 A B C R b c)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
