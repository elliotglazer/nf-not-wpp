import NAR4C087C001Part001

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

theorem nb087_compact_fv_empty_0014 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_001 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0014 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_001 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_001, fv_syn_c1c] using (nb087_compact_fv_empty_0014 A B C R)

theorem nb087_compact_fv_empty_0015 (C : Class) (d : Var) : (nb087_alpha_dummy_003 C d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0015 (C : Class) (d : Var) : (nb087_alpha_dummy_003 C d) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_003, fv_syn_c1c] using (nb087_compact_fv_empty_0015 C d)

theorem nb087_compact_fv_empty_0016 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_007 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0016 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_007 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_007, fv_syn_c1c] using (nb087_compact_fv_empty_0016 A B C R)

theorem nb087_compact_fv_empty_0017 (C : Class) (d : Var) : (nb087_alpha_dummy_008 C d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0017 (C : Class) (d : Var) : (nb087_alpha_dummy_008 C d) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_008, fv_syn_c1c] using (nb087_compact_fv_empty_0017 C d)

theorem nb087_compact_fv_empty_0018 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_005 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0018 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_005 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_005, fv_syn_c1c] using (nb087_compact_fv_empty_0018 A B C R)

theorem nb087_compact_fv_empty_0019 (C : Class) (d : Var) : (nb087_alpha_dummy_006 C d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0019 (C : Class) (d : Var) : (nb087_alpha_dummy_006 C d) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_006, fv_syn_c1c] using (nb087_compact_fv_empty_0019 C d)

theorem nb087_compact_fv_empty_0020 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_000 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0020 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_000 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_000, fv_syn_c1c] using (nb087_compact_fv_empty_0020 A B C R)

theorem nb087_compact_fv_empty_0021 (d : Var) : d ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0021 (d : Var) : d ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb087_compact_fv_empty_0021 d)

theorem nb087_compact_envfresh_0000 (A : Class) (B : Class) (C : Class) (R : Class) (d : Var) : TEnvFresh [((nb087_alpha_dummy_019 A B C R), (nb087_alpha_dummy_022 C d)), ((nb087_alpha_dummy_018 A B C R), (nb087_alpha_dummy_021 C d)), ((nb087_alpha_dummy_017 A B C R), (nb087_alpha_dummy_020 C d)), ((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016 C d)), ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)), ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)), ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)), ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)), ((nb087_alpha_dummy_007 A B C R), (nb087_alpha_dummy_008 C d)), ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)), ((nb087_alpha_dummy_000 A B C R), d)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb087_alpha_dummy_019 A B C R) (nb087_alpha_dummy_022 C d) (nb087_wpp_notmem_0000 A B C R) (nb087_wpp_notmem_0001 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_018 A B C R) (nb087_alpha_dummy_021 C d) (nb087_wpp_notmem_0002 A B C R) (nb087_wpp_notmem_0003 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_017 A B C R) (nb087_alpha_dummy_020 C d) (nb087_wpp_notmem_0004 A B C R) (nb087_wpp_notmem_0005 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_015 A B C R) (nb087_alpha_dummy_016 C d) (nb087_wpp_notmem_0006 A B C R) (nb087_wpp_notmem_0007 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_011 A B C R) (nb087_alpha_dummy_013 C d) (nb087_wpp_notmem_0008 A B C R) (nb087_wpp_notmem_0009 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_012 A B C R) (nb087_alpha_dummy_014 C d) (nb087_wpp_notmem_0010 A B C R) (nb087_wpp_notmem_0011 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_002 A B C R) (nb087_alpha_dummy_004 C d) (nb087_wpp_notmem_0012 A B C R) (nb087_wpp_notmem_0013 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_001 A B C R) (nb087_alpha_dummy_003 C d) (nb087_wpp_notmem_0014 A B C R) (nb087_wpp_notmem_0015 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_007 A B C R) (nb087_alpha_dummy_008 C d) (nb087_wpp_notmem_0016 A B C R) (nb087_wpp_notmem_0017 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_005 A B C R) (nb087_alpha_dummy_006 C d) (nb087_wpp_notmem_0018 A B C R) (nb087_wpp_notmem_0019 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_000 A B C R) d (nb087_wpp_notmem_0020 A B C R) (nb087_wpp_notmem_0021 d) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))

noncomputable def nb087_wpp_refl_0000 (A : Class) (B : Class) (C : Class) (R : Class) (d : Var) : TReflOn [((nb087_alpha_dummy_019 A B C R), (nb087_alpha_dummy_022 C d)), ((nb087_alpha_dummy_018 A B C R), (nb087_alpha_dummy_021 C d)), ((nb087_alpha_dummy_017 A B C R), (nb087_alpha_dummy_020 C d)), ((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016 C d)), ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)), ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)), ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)), ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)), ((nb087_alpha_dummy_007 A B C R), (nb087_alpha_dummy_008 C d)), ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)), ((nb087_alpha_dummy_000 A B C R), d)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb087_compact_envfresh_0000 A B C R d)

theorem nb087_wpp_notmem_0022 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_019 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_019, fv_syn_c0] using (nb087_compact_fv_empty_0000 A B C R)

theorem nb087_wpp_notmem_0023 (C : Class) (d : Var) : (nb087_alpha_dummy_022 C d) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_022, fv_syn_c0] using (nb087_compact_fv_empty_0001 C d)

theorem nb087_wpp_notmem_0024 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_018 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_018, fv_syn_c0] using (nb087_compact_fv_empty_0002 A B C R)

theorem nb087_wpp_notmem_0025 (C : Class) (d : Var) : (nb087_alpha_dummy_021 C d) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_021, fv_syn_c0] using (nb087_compact_fv_empty_0003 C d)

theorem nb087_wpp_notmem_0026 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_017 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_017, fv_syn_c0] using (nb087_compact_fv_empty_0004 A B C R)

theorem nb087_wpp_notmem_0027 (C : Class) (d : Var) : (nb087_alpha_dummy_020 C d) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_020, fv_syn_c0] using (nb087_compact_fv_empty_0005 C d)

theorem nb087_wpp_notmem_0028 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_015 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_015, fv_syn_c0] using (nb087_compact_fv_empty_0006 A B C R)

theorem nb087_wpp_notmem_0029 (C : Class) (d : Var) : (nb087_alpha_dummy_016 C d) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_016, fv_syn_c0] using (nb087_compact_fv_empty_0007 C d)

theorem nb087_wpp_notmem_0030 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_011 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_011, fv_syn_c0] using (nb087_compact_fv_empty_0008 A B C R)

theorem nb087_wpp_notmem_0031 (C : Class) (d : Var) : (nb087_alpha_dummy_013 C d) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_013, fv_syn_c0] using (nb087_compact_fv_empty_0009 C d)

theorem nb087_wpp_notmem_0032 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_012 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_012, fv_syn_c0] using (nb087_compact_fv_empty_0010 A B C R)

theorem nb087_wpp_notmem_0033 (C : Class) (d : Var) : (nb087_alpha_dummy_014 C d) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_014, fv_syn_c0] using (nb087_compact_fv_empty_0011 C d)

theorem nb087_wpp_notmem_0034 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_002 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_002, fv_syn_c0] using (nb087_compact_fv_empty_0012 A B C R)

theorem nb087_wpp_notmem_0035 (C : Class) (d : Var) : (nb087_alpha_dummy_004 C d) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_004, fv_syn_c0] using (nb087_compact_fv_empty_0013 C d)

theorem nb087_wpp_notmem_0036 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_001 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_001, fv_syn_c0] using (nb087_compact_fv_empty_0014 A B C R)

theorem nb087_wpp_notmem_0037 (C : Class) (d : Var) : (nb087_alpha_dummy_003 C d) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_003, fv_syn_c0] using (nb087_compact_fv_empty_0015 C d)

theorem nb087_wpp_notmem_0038 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_007 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_007, fv_syn_c0] using (nb087_compact_fv_empty_0016 A B C R)

theorem nb087_wpp_notmem_0039 (C : Class) (d : Var) : (nb087_alpha_dummy_008 C d) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_008, fv_syn_c0] using (nb087_compact_fv_empty_0017 C d)

theorem nb087_wpp_notmem_0040 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_005 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_005, fv_syn_c0] using (nb087_compact_fv_empty_0018 A B C R)

theorem nb087_wpp_notmem_0041 (C : Class) (d : Var) : (nb087_alpha_dummy_006 C d) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_006, fv_syn_c0] using (nb087_compact_fv_empty_0019 C d)

theorem nb087_wpp_notmem_0042 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_000 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_000, fv_syn_c0] using (nb087_compact_fv_empty_0020 A B C R)

theorem nb087_wpp_notmem_0043 (d : Var) : d ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb087_compact_fv_empty_0021 d)

theorem nb087_compact_envfresh_0001 (A : Class) (B : Class) (C : Class) (R : Class) (d : Var) : TEnvFresh [((nb087_alpha_dummy_019 A B C R), (nb087_alpha_dummy_022 C d)), ((nb087_alpha_dummy_018 A B C R), (nb087_alpha_dummy_021 C d)), ((nb087_alpha_dummy_017 A B C R), (nb087_alpha_dummy_020 C d)), ((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016 C d)), ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)), ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)), ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)), ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)), ((nb087_alpha_dummy_007 A B C R), (nb087_alpha_dummy_008 C d)), ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)), ((nb087_alpha_dummy_000 A B C R), d)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb087_alpha_dummy_019 A B C R) (nb087_alpha_dummy_022 C d) (nb087_wpp_notmem_0022 A B C R) (nb087_wpp_notmem_0023 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_018 A B C R) (nb087_alpha_dummy_021 C d) (nb087_wpp_notmem_0024 A B C R) (nb087_wpp_notmem_0025 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_017 A B C R) (nb087_alpha_dummy_020 C d) (nb087_wpp_notmem_0026 A B C R) (nb087_wpp_notmem_0027 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_015 A B C R) (nb087_alpha_dummy_016 C d) (nb087_wpp_notmem_0028 A B C R) (nb087_wpp_notmem_0029 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_011 A B C R) (nb087_alpha_dummy_013 C d) (nb087_wpp_notmem_0030 A B C R) (nb087_wpp_notmem_0031 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_012 A B C R) (nb087_alpha_dummy_014 C d) (nb087_wpp_notmem_0032 A B C R) (nb087_wpp_notmem_0033 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_002 A B C R) (nb087_alpha_dummy_004 C d) (nb087_wpp_notmem_0034 A B C R) (nb087_wpp_notmem_0035 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_001 A B C R) (nb087_alpha_dummy_003 C d) (nb087_wpp_notmem_0036 A B C R) (nb087_wpp_notmem_0037 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_007 A B C R) (nb087_alpha_dummy_008 C d) (nb087_wpp_notmem_0038 A B C R) (nb087_wpp_notmem_0039 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_005 A B C R) (nb087_alpha_dummy_006 C d) (nb087_wpp_notmem_0040 A B C R) (nb087_wpp_notmem_0041 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_000 A B C R) d (nb087_wpp_notmem_0042 A B C R) (nb087_wpp_notmem_0043 d) (TEnvFresh.nil ((syn_c0)).fv))))))))))))

noncomputable def nb087_wpp_refl_0001 (A : Class) (B : Class) (C : Class) (R : Class) (d : Var) : TReflOn [((nb087_alpha_dummy_019 A B C R), (nb087_alpha_dummy_022 C d)), ((nb087_alpha_dummy_018 A B C R), (nb087_alpha_dummy_021 C d)), ((nb087_alpha_dummy_017 A B C R), (nb087_alpha_dummy_020 C d)), ((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016 C d)), ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)), ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)), ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)), ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)), ((nb087_alpha_dummy_007 A B C R), (nb087_alpha_dummy_008 C d)), ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)), ((nb087_alpha_dummy_000 A B C R), d)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb087_compact_envfresh_0001 A B C R d)

theorem nb087_wpp_notmem_0044 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_015 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb087_alpha_dummy_015, fv_syn_cnnc] using (nb087_compact_fv_empty_0006 A B C R)

theorem nb087_wpp_notmem_0045 (C : Class) (d : Var) : (nb087_alpha_dummy_016 C d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb087_alpha_dummy_016, fv_syn_cnnc] using (nb087_compact_fv_empty_0007 C d)

theorem nb087_wpp_notmem_0046 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_011 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb087_alpha_dummy_011, fv_syn_cnnc] using (nb087_compact_fv_empty_0008 A B C R)

theorem nb087_wpp_notmem_0047 (C : Class) (d : Var) : (nb087_alpha_dummy_013 C d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb087_alpha_dummy_013, fv_syn_cnnc] using (nb087_compact_fv_empty_0009 C d)

theorem nb087_wpp_notmem_0048 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_012 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb087_alpha_dummy_012, fv_syn_cnnc] using (nb087_compact_fv_empty_0010 A B C R)

theorem nb087_wpp_notmem_0049 (C : Class) (d : Var) : (nb087_alpha_dummy_014 C d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb087_alpha_dummy_014, fv_syn_cnnc] using (nb087_compact_fv_empty_0011 C d)

theorem nb087_wpp_notmem_0050 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_002 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb087_alpha_dummy_002, fv_syn_cnnc] using (nb087_compact_fv_empty_0012 A B C R)

theorem nb087_wpp_notmem_0051 (C : Class) (d : Var) : (nb087_alpha_dummy_004 C d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb087_alpha_dummy_004, fv_syn_cnnc] using (nb087_compact_fv_empty_0013 C d)

theorem nb087_wpp_notmem_0052 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_001 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb087_alpha_dummy_001, fv_syn_cnnc] using (nb087_compact_fv_empty_0014 A B C R)

theorem nb087_wpp_notmem_0053 (C : Class) (d : Var) : (nb087_alpha_dummy_003 C d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb087_alpha_dummy_003, fv_syn_cnnc] using (nb087_compact_fv_empty_0015 C d)

theorem nb087_wpp_notmem_0054 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_007 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb087_alpha_dummy_007, fv_syn_cnnc] using (nb087_compact_fv_empty_0016 A B C R)

theorem nb087_wpp_notmem_0055 (C : Class) (d : Var) : (nb087_alpha_dummy_008 C d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb087_alpha_dummy_008, fv_syn_cnnc] using (nb087_compact_fv_empty_0017 C d)

theorem nb087_wpp_notmem_0056 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_005 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb087_alpha_dummy_005, fv_syn_cnnc] using (nb087_compact_fv_empty_0018 A B C R)

theorem nb087_wpp_notmem_0057 (C : Class) (d : Var) : (nb087_alpha_dummy_006 C d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb087_alpha_dummy_006, fv_syn_cnnc] using (nb087_compact_fv_empty_0019 C d)

theorem nb087_wpp_notmem_0058 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_000 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb087_alpha_dummy_000, fv_syn_cnnc] using (nb087_compact_fv_empty_0020 A B C R)

theorem nb087_wpp_notmem_0059 (d : Var) : d ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb087_compact_fv_empty_0021 d)

theorem nb087_compact_envfresh_0002 (A : Class) (B : Class) (C : Class) (R : Class) (d : Var) : TEnvFresh [((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016 C d)), ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)), ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)), ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)), ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)), ((nb087_alpha_dummy_007 A B C R), (nb087_alpha_dummy_008 C d)), ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)), ((nb087_alpha_dummy_000 A B C R), d)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb087_alpha_dummy_015 A B C R) (nb087_alpha_dummy_016 C d) (nb087_wpp_notmem_0044 A B C R) (nb087_wpp_notmem_0045 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_011 A B C R) (nb087_alpha_dummy_013 C d) (nb087_wpp_notmem_0046 A B C R) (nb087_wpp_notmem_0047 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_012 A B C R) (nb087_alpha_dummy_014 C d) (nb087_wpp_notmem_0048 A B C R) (nb087_wpp_notmem_0049 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_002 A B C R) (nb087_alpha_dummy_004 C d) (nb087_wpp_notmem_0050 A B C R) (nb087_wpp_notmem_0051 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_001 A B C R) (nb087_alpha_dummy_003 C d) (nb087_wpp_notmem_0052 A B C R) (nb087_wpp_notmem_0053 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_007 A B C R) (nb087_alpha_dummy_008 C d) (nb087_wpp_notmem_0054 A B C R) (nb087_wpp_notmem_0055 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_005 A B C R) (nb087_alpha_dummy_006 C d) (nb087_wpp_notmem_0056 A B C R) (nb087_wpp_notmem_0057 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_000 A B C R) d (nb087_wpp_notmem_0058 A B C R) (nb087_wpp_notmem_0059 d) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))

noncomputable def nb087_wpp_refl_0002 (A : Class) (B : Class) (C : Class) (R : Class) (d : Var) : TReflOn [((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016 C d)), ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)), ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)), ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)), ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)), ((nb087_alpha_dummy_007 A B C R), (nb087_alpha_dummy_008 C d)), ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)), ((nb087_alpha_dummy_000 A B C R), d)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb087_compact_envfresh_0002 A B C R d)

theorem nb087_focused_notmem_0000 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_002 A B C R) ∉ C.fv := by
  change freshVar (((syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R)))).fv ∪ (C).fv) 1 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun u hu => Finset.mem_union_right _ (hu))

theorem nb087_focused_notmem_0001 (C : Class) (d : Var) : (nb087_alpha_dummy_004 C d) ∉ C.fv := by
  change freshVar (((syn_csn (Class.cv d))).fv ∪ (C).fv) 1 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun u hu => Finset.mem_union_right _ (hu))

theorem nb087_focused_notmem_0002 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_001 A B C R) ∉ C.fv := by
  change freshVar (((syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R)))).fv ∪ (C).fv) 0 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_right _ (hu))

theorem nb087_focused_notmem_0003 (C : Class) (d : Var) : (nb087_alpha_dummy_003 C d) ∉ C.fv := by
  change freshVar (((syn_csn (Class.cv d))).fv ∪ (C).fv) 0 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_right _ (hu))

theorem nb087_focused_notmem_0004 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_033 A B C R) ∉ C.fv := by
  change freshVar (((Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) C (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) C (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))) (syn_csn (syn_c0c))))))).fv) 0 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (((fv_class_cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) C (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))) (syn_csn (syn_c0c)))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb087_focused_notmem_0002 A B C R)) (h_eq ▸ hu)), (((fv_syn_wrex (nb087_alpha_dummy_002 A B C R) C (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))) (syn_csn (syn_c0c))))).symm ▸ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb087_focused_notmem_0000 A B C R)) (h_eq ▸ hu)), (hu)⟩))))⟩))))

theorem nb087_focused_notmem_0005 (C : Class) (d : Var) : (nb087_alpha_dummy_034 C d) ∉ C.fv := by
  change freshVar (((Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) C (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) C (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))) (syn_csn (syn_c0c))))))).fv) 0 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (((fv_class_cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) C (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))) (syn_csn (syn_c0c)))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb087_focused_notmem_0003 C d)) (h_eq ▸ hu)), (((fv_syn_wrex (nb087_alpha_dummy_004 C d) C (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))) (syn_csn (syn_c0c))))).symm ▸ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb087_focused_notmem_0001 C d)) (h_eq ▸ hu)), (hu)⟩))))⟩))))

theorem nb087_focused_notmem_0006 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_005 A B C R) ∉ C.fv := by
  change freshVar (((syn_ccompl (Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) (syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R))) (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) C (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))) (syn_csn (syn_c0c)))))))).fv) 0 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_right _ (((fv_syn_ccompl (Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) C (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))) (syn_csn (syn_c0c))))))).symm ▸ (((fv_class_cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) C (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))) (syn_csn (syn_c0c)))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb087_focused_notmem_0002 A B C R)) (h_eq ▸ hu)), (((fv_syn_wrex (nb087_alpha_dummy_002 A B C R) C (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))) (syn_csn (syn_c0c))))).symm ▸ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb087_focused_notmem_0000 A B C R)) (h_eq ▸ hu)), (hu)⟩))))⟩))))))

theorem nb087_focused_notmem_0007 (C : Class) (d : Var) : (nb087_alpha_dummy_006 C d) ∉ C.fv := by
  change freshVar (((syn_ccompl (Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) (syn_csn (Class.cv d)) (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d)))))))).fv ∪ ((syn_ccompl (Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) C (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))) (syn_csn (syn_c0c)))))))).fv) 0 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_right _ (((fv_syn_ccompl (Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) C (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))) (syn_csn (syn_c0c))))))).symm ▸ (((fv_class_cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) C (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))) (syn_csn (syn_c0c)))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb087_focused_notmem_0003 C d)) (h_eq ▸ hu)), (((fv_syn_wrex (nb087_alpha_dummy_004 C d) C (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))) (syn_csn (syn_c0c))))).symm ▸ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb087_focused_notmem_0001 C d)) (h_eq ▸ hu)), (hu)⟩))))⟩))))))

theorem nb087_focused_notmem_0008 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_000 A B C R) ∉ C.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_right _ (hu))

theorem nb087_compact_envfresh_0003 (A : Class) (B : Class) (C : Class) (R : Class) (d : Var) (dv_C_d : d ∉ C.fv) : TEnvFresh [((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)), ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)), ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)), ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)), ((nb087_alpha_dummy_000 A B C R), d)] C.fv := by
  exact (TEnvFresh.consFresh (nb087_alpha_dummy_002 A B C R) (nb087_alpha_dummy_004 C d) (nb087_focused_notmem_0000 A B C R) (nb087_focused_notmem_0001 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_001 A B C R) (nb087_alpha_dummy_003 C d) (nb087_focused_notmem_0002 A B C R) (nb087_focused_notmem_0003 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_033 A B C R) (nb087_alpha_dummy_034 C d) (nb087_focused_notmem_0004 A B C R) (nb087_focused_notmem_0005 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_005 A B C R) (nb087_alpha_dummy_006 C d) (nb087_focused_notmem_0006 A B C R) (nb087_focused_notmem_0007 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_000 A B C R) d (nb087_focused_notmem_0008 A B C R) dv_C_d (TEnvFresh.nil C.fv))))))

noncomputable def nb087_focused_refl_0000 (A : Class) (B : Class) (C : Class) (R : Class) (d : Var) (dv_C_d : d ∉ C.fv) : TReflOn [((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)), ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)), ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)), ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)), ((nb087_alpha_dummy_000 A B C R), d)] C.fv :=
  TEnvFresh.reflOn (nb087_compact_envfresh_0003 A B C R d dv_C_d)

theorem nb087_compact_fv_empty_0022 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_037 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0060 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_037 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_037, fv_syn_c1c] using (nb087_compact_fv_empty_0022 A B C R)

theorem nb087_compact_fv_empty_0023 (C : Class) (d : Var) : (nb087_alpha_dummy_038 C d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0061 (C : Class) (d : Var) : (nb087_alpha_dummy_038 C d) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_038, fv_syn_c1c] using (nb087_compact_fv_empty_0023 C d)

theorem nb087_compact_fv_empty_0024 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_035 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0062 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_035 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_035, fv_syn_c1c] using (nb087_compact_fv_empty_0024 A B C R)

theorem nb087_compact_fv_empty_0025 (C : Class) (d : Var) : (nb087_alpha_dummy_036 C d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0063 (C : Class) (d : Var) : (nb087_alpha_dummy_036 C d) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_036, fv_syn_c1c] using (nb087_compact_fv_empty_0025 C d)

theorem nb087_compact_fv_empty_0026 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_033 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0064 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_033 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_033, fv_syn_c1c] using (nb087_compact_fv_empty_0026 A B C R)

theorem nb087_compact_fv_empty_0027 (C : Class) (d : Var) : (nb087_alpha_dummy_034 C d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0065 (C : Class) (d : Var) : (nb087_alpha_dummy_034 C d) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_034, fv_syn_c1c] using (nb087_compact_fv_empty_0027 C d)

theorem nb087_compact_envfresh_0004 (A : Class) (B : Class) (C : Class) (R : Class) (d : Var) : TEnvFresh [((nb087_alpha_dummy_019 A B C R), (nb087_alpha_dummy_022 C d)), ((nb087_alpha_dummy_018 A B C R), (nb087_alpha_dummy_021 C d)), ((nb087_alpha_dummy_017 A B C R), (nb087_alpha_dummy_020 C d)), ((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016 C d)), ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)), ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)), ((nb087_alpha_dummy_037 A B C R), (nb087_alpha_dummy_038 C d)), ((nb087_alpha_dummy_035 A B C R), (nb087_alpha_dummy_036 C d)), ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)), ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)), ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)), ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)), ((nb087_alpha_dummy_000 A B C R), d)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb087_alpha_dummy_019 A B C R) (nb087_alpha_dummy_022 C d) (nb087_wpp_notmem_0000 A B C R) (nb087_wpp_notmem_0001 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_018 A B C R) (nb087_alpha_dummy_021 C d) (nb087_wpp_notmem_0002 A B C R) (nb087_wpp_notmem_0003 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_017 A B C R) (nb087_alpha_dummy_020 C d) (nb087_wpp_notmem_0004 A B C R) (nb087_wpp_notmem_0005 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_015 A B C R) (nb087_alpha_dummy_016 C d) (nb087_wpp_notmem_0006 A B C R) (nb087_wpp_notmem_0007 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_011 A B C R) (nb087_alpha_dummy_013 C d) (nb087_wpp_notmem_0008 A B C R) (nb087_wpp_notmem_0009 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_012 A B C R) (nb087_alpha_dummy_014 C d) (nb087_wpp_notmem_0010 A B C R) (nb087_wpp_notmem_0011 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_037 A B C R) (nb087_alpha_dummy_038 C d) (nb087_wpp_notmem_0060 A B C R) (nb087_wpp_notmem_0061 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_035 A B C R) (nb087_alpha_dummy_036 C d) (nb087_wpp_notmem_0062 A B C R) (nb087_wpp_notmem_0063 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_002 A B C R) (nb087_alpha_dummy_004 C d) (nb087_wpp_notmem_0012 A B C R) (nb087_wpp_notmem_0013 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_001 A B C R) (nb087_alpha_dummy_003 C d) (nb087_wpp_notmem_0014 A B C R) (nb087_wpp_notmem_0015 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_033 A B C R) (nb087_alpha_dummy_034 C d) (nb087_wpp_notmem_0064 A B C R) (nb087_wpp_notmem_0065 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_005 A B C R) (nb087_alpha_dummy_006 C d) (nb087_wpp_notmem_0018 A B C R) (nb087_wpp_notmem_0019 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_000 A B C R) d (nb087_wpp_notmem_0020 A B C R) (nb087_wpp_notmem_0021 d) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))

noncomputable def nb087_wpp_refl_0003 (A : Class) (B : Class) (C : Class) (R : Class) (d : Var) : TReflOn [((nb087_alpha_dummy_019 A B C R), (nb087_alpha_dummy_022 C d)), ((nb087_alpha_dummy_018 A B C R), (nb087_alpha_dummy_021 C d)), ((nb087_alpha_dummy_017 A B C R), (nb087_alpha_dummy_020 C d)), ((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016 C d)), ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)), ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)), ((nb087_alpha_dummy_037 A B C R), (nb087_alpha_dummy_038 C d)), ((nb087_alpha_dummy_035 A B C R), (nb087_alpha_dummy_036 C d)), ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)), ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)), ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)), ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)), ((nb087_alpha_dummy_000 A B C R), d)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb087_compact_envfresh_0004 A B C R d)

theorem nb087_wpp_notmem_0066 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_037 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_037, fv_syn_c0] using (nb087_compact_fv_empty_0022 A B C R)

theorem nb087_wpp_notmem_0067 (C : Class) (d : Var) : (nb087_alpha_dummy_038 C d) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_038, fv_syn_c0] using (nb087_compact_fv_empty_0023 C d)

theorem nb087_wpp_notmem_0068 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_035 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_035, fv_syn_c0] using (nb087_compact_fv_empty_0024 A B C R)

theorem nb087_wpp_notmem_0069 (C : Class) (d : Var) : (nb087_alpha_dummy_036 C d) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_036, fv_syn_c0] using (nb087_compact_fv_empty_0025 C d)

theorem nb087_wpp_notmem_0070 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_033 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_033, fv_syn_c0] using (nb087_compact_fv_empty_0026 A B C R)

theorem nb087_wpp_notmem_0071 (C : Class) (d : Var) : (nb087_alpha_dummy_034 C d) ∉ ((syn_c0)).fv := by
  simpa only [nb087_alpha_dummy_034, fv_syn_c0] using (nb087_compact_fv_empty_0027 C d)

theorem nb087_compact_envfresh_0005 (A : Class) (B : Class) (C : Class) (R : Class) (d : Var) : TEnvFresh [((nb087_alpha_dummy_019 A B C R), (nb087_alpha_dummy_022 C d)), ((nb087_alpha_dummy_018 A B C R), (nb087_alpha_dummy_021 C d)), ((nb087_alpha_dummy_017 A B C R), (nb087_alpha_dummy_020 C d)), ((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016 C d)), ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)), ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)), ((nb087_alpha_dummy_037 A B C R), (nb087_alpha_dummy_038 C d)), ((nb087_alpha_dummy_035 A B C R), (nb087_alpha_dummy_036 C d)), ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)), ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)), ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)), ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)), ((nb087_alpha_dummy_000 A B C R), d)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb087_alpha_dummy_019 A B C R) (nb087_alpha_dummy_022 C d) (nb087_wpp_notmem_0022 A B C R) (nb087_wpp_notmem_0023 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_018 A B C R) (nb087_alpha_dummy_021 C d) (nb087_wpp_notmem_0024 A B C R) (nb087_wpp_notmem_0025 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_017 A B C R) (nb087_alpha_dummy_020 C d) (nb087_wpp_notmem_0026 A B C R) (nb087_wpp_notmem_0027 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_015 A B C R) (nb087_alpha_dummy_016 C d) (nb087_wpp_notmem_0028 A B C R) (nb087_wpp_notmem_0029 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_011 A B C R) (nb087_alpha_dummy_013 C d) (nb087_wpp_notmem_0030 A B C R) (nb087_wpp_notmem_0031 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_012 A B C R) (nb087_alpha_dummy_014 C d) (nb087_wpp_notmem_0032 A B C R) (nb087_wpp_notmem_0033 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_037 A B C R) (nb087_alpha_dummy_038 C d) (nb087_wpp_notmem_0066 A B C R) (nb087_wpp_notmem_0067 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_035 A B C R) (nb087_alpha_dummy_036 C d) (nb087_wpp_notmem_0068 A B C R) (nb087_wpp_notmem_0069 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_002 A B C R) (nb087_alpha_dummy_004 C d) (nb087_wpp_notmem_0034 A B C R) (nb087_wpp_notmem_0035 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_001 A B C R) (nb087_alpha_dummy_003 C d) (nb087_wpp_notmem_0036 A B C R) (nb087_wpp_notmem_0037 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_033 A B C R) (nb087_alpha_dummy_034 C d) (nb087_wpp_notmem_0070 A B C R) (nb087_wpp_notmem_0071 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_005 A B C R) (nb087_alpha_dummy_006 C d) (nb087_wpp_notmem_0040 A B C R) (nb087_wpp_notmem_0041 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_000 A B C R) d (nb087_wpp_notmem_0042 A B C R) (nb087_wpp_notmem_0043 d) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))

noncomputable def nb087_wpp_refl_0004 (A : Class) (B : Class) (C : Class) (R : Class) (d : Var) : TReflOn [((nb087_alpha_dummy_019 A B C R), (nb087_alpha_dummy_022 C d)), ((nb087_alpha_dummy_018 A B C R), (nb087_alpha_dummy_021 C d)), ((nb087_alpha_dummy_017 A B C R), (nb087_alpha_dummy_020 C d)), ((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016 C d)), ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)), ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)), ((nb087_alpha_dummy_037 A B C R), (nb087_alpha_dummy_038 C d)), ((nb087_alpha_dummy_035 A B C R), (nb087_alpha_dummy_036 C d)), ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)), ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)), ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)), ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)), ((nb087_alpha_dummy_000 A B C R), d)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb087_compact_envfresh_0005 A B C R d)

theorem nb087_wpp_notmem_0072 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_037 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb087_alpha_dummy_037, fv_syn_cnnc] using (nb087_compact_fv_empty_0022 A B C R)

theorem nb087_wpp_notmem_0073 (C : Class) (d : Var) : (nb087_alpha_dummy_038 C d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb087_alpha_dummy_038, fv_syn_cnnc] using (nb087_compact_fv_empty_0023 C d)

theorem nb087_wpp_notmem_0074 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_035 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb087_alpha_dummy_035, fv_syn_cnnc] using (nb087_compact_fv_empty_0024 A B C R)

theorem nb087_wpp_notmem_0075 (C : Class) (d : Var) : (nb087_alpha_dummy_036 C d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb087_alpha_dummy_036, fv_syn_cnnc] using (nb087_compact_fv_empty_0025 C d)

theorem nb087_wpp_notmem_0076 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_033 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb087_alpha_dummy_033, fv_syn_cnnc] using (nb087_compact_fv_empty_0026 A B C R)

theorem nb087_wpp_notmem_0077 (C : Class) (d : Var) : (nb087_alpha_dummy_034 C d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb087_alpha_dummy_034, fv_syn_cnnc] using (nb087_compact_fv_empty_0027 C d)

theorem nb087_compact_envfresh_0006 (A : Class) (B : Class) (C : Class) (R : Class) (d : Var) : TEnvFresh [((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016 C d)), ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)), ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)), ((nb087_alpha_dummy_037 A B C R), (nb087_alpha_dummy_038 C d)), ((nb087_alpha_dummy_035 A B C R), (nb087_alpha_dummy_036 C d)), ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)), ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)), ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)), ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)), ((nb087_alpha_dummy_000 A B C R), d)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb087_alpha_dummy_015 A B C R) (nb087_alpha_dummy_016 C d) (nb087_wpp_notmem_0044 A B C R) (nb087_wpp_notmem_0045 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_011 A B C R) (nb087_alpha_dummy_013 C d) (nb087_wpp_notmem_0046 A B C R) (nb087_wpp_notmem_0047 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_012 A B C R) (nb087_alpha_dummy_014 C d) (nb087_wpp_notmem_0048 A B C R) (nb087_wpp_notmem_0049 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_037 A B C R) (nb087_alpha_dummy_038 C d) (nb087_wpp_notmem_0072 A B C R) (nb087_wpp_notmem_0073 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_035 A B C R) (nb087_alpha_dummy_036 C d) (nb087_wpp_notmem_0074 A B C R) (nb087_wpp_notmem_0075 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_002 A B C R) (nb087_alpha_dummy_004 C d) (nb087_wpp_notmem_0050 A B C R) (nb087_wpp_notmem_0051 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_001 A B C R) (nb087_alpha_dummy_003 C d) (nb087_wpp_notmem_0052 A B C R) (nb087_wpp_notmem_0053 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_033 A B C R) (nb087_alpha_dummy_034 C d) (nb087_wpp_notmem_0076 A B C R) (nb087_wpp_notmem_0077 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_005 A B C R) (nb087_alpha_dummy_006 C d) (nb087_wpp_notmem_0056 A B C R) (nb087_wpp_notmem_0057 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_000 A B C R) d (nb087_wpp_notmem_0058 A B C R) (nb087_wpp_notmem_0059 d) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))

noncomputable def nb087_wpp_refl_0005 (A : Class) (B : Class) (C : Class) (R : Class) (d : Var) : TReflOn [((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016 C d)), ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)), ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)), ((nb087_alpha_dummy_037 A B C R), (nb087_alpha_dummy_038 C d)), ((nb087_alpha_dummy_035 A B C R), (nb087_alpha_dummy_036 C d)), ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)), ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)), ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)), ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)), ((nb087_alpha_dummy_000 A B C R), d)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb087_compact_envfresh_0006 A B C R d)

theorem nb087_wpp_notmem_0078 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_035 A B C R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb087_alpha_dummy_035, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb087_compact_fv_empty_0024 A B C R)

theorem nb087_wpp_notmem_0079 (C : Class) (d : Var) : (nb087_alpha_dummy_036 C d) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb087_alpha_dummy_036, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb087_compact_fv_empty_0025 C d)

theorem nb087_wpp_notmem_0080 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_002 A B C R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb087_alpha_dummy_002, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb087_compact_fv_empty_0012 A B C R)

theorem nb087_wpp_notmem_0081 (C : Class) (d : Var) : (nb087_alpha_dummy_004 C d) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb087_alpha_dummy_004, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb087_compact_fv_empty_0013 C d)

theorem nb087_wpp_notmem_0082 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_001 A B C R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb087_alpha_dummy_001, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb087_compact_fv_empty_0014 A B C R)

theorem nb087_wpp_notmem_0083 (C : Class) (d : Var) : (nb087_alpha_dummy_003 C d) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb087_alpha_dummy_003, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb087_compact_fv_empty_0015 C d)

theorem nb087_wpp_notmem_0084 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_033 A B C R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb087_alpha_dummy_033, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb087_compact_fv_empty_0026 A B C R)

theorem nb087_wpp_notmem_0085 (C : Class) (d : Var) : (nb087_alpha_dummy_034 C d) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb087_alpha_dummy_034, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb087_compact_fv_empty_0027 C d)

theorem nb087_wpp_notmem_0086 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_005 A B C R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb087_alpha_dummy_005, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb087_compact_fv_empty_0018 A B C R)

theorem nb087_wpp_notmem_0087 (C : Class) (d : Var) : (nb087_alpha_dummy_006 C d) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb087_alpha_dummy_006, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb087_compact_fv_empty_0019 C d)

theorem nb087_wpp_notmem_0088 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_000 A B C R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb087_alpha_dummy_000, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb087_compact_fv_empty_0020 A B C R)

theorem nb087_wpp_notmem_0089 (d : Var) : d ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb087_compact_fv_empty_0021 d)

theorem nb087_compact_envfresh_0007 (A : Class) (B : Class) (C : Class) (R : Class) (d : Var) : TEnvFresh [((nb087_alpha_dummy_035 A B C R), (nb087_alpha_dummy_036 C d)), ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)), ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)), ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)), ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)), ((nb087_alpha_dummy_000 A B C R), d)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb087_alpha_dummy_035 A B C R) (nb087_alpha_dummy_036 C d) (nb087_wpp_notmem_0078 A B C R) (nb087_wpp_notmem_0079 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_002 A B C R) (nb087_alpha_dummy_004 C d) (nb087_wpp_notmem_0080 A B C R) (nb087_wpp_notmem_0081 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_001 A B C R) (nb087_alpha_dummy_003 C d) (nb087_wpp_notmem_0082 A B C R) (nb087_wpp_notmem_0083 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_033 A B C R) (nb087_alpha_dummy_034 C d) (nb087_wpp_notmem_0084 A B C R) (nb087_wpp_notmem_0085 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_005 A B C R) (nb087_alpha_dummy_006 C d) (nb087_wpp_notmem_0086 A B C R) (nb087_wpp_notmem_0087 C d) (TEnvFresh.consFresh (nb087_alpha_dummy_000 A B C R) d (nb087_wpp_notmem_0088 A B C R) (nb087_wpp_notmem_0089 d) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))

noncomputable def nb087_wpp_refl_0006 (A : Class) (B : Class) (C : Class) (R : Class) (d : Var) : TReflOn [((nb087_alpha_dummy_035 A B C R), (nb087_alpha_dummy_036 C d)), ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)), ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)), ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)), ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)), ((nb087_alpha_dummy_000 A B C R), d)] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb087_compact_envfresh_0007 A B C R d)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
