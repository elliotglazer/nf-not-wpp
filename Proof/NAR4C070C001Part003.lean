import NAR4C070C001Part002

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

theorem nb070_compact_fv_empty_0035 (x : Var) : (nb070_alpha_dummy_026 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0053 (x : Var) : (nb070_alpha_dummy_026 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_026, fv_syn_c1c] using (nb070_compact_fv_empty_0035 x)

theorem nb070_compact_fv_empty_0036 (A : Class) : (nb070_alpha_dummy_030 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0054 (A : Class) : (nb070_alpha_dummy_030 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_030, fv_syn_c1c] using (nb070_compact_fv_empty_0036 A)

theorem nb070_compact_fv_empty_0037 (x : Var) : (nb070_alpha_dummy_031 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0055 (x : Var) : (nb070_alpha_dummy_031 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_031, fv_syn_c1c] using (nb070_compact_fv_empty_0037 x)

theorem nb070_compact_fv_empty_0038 (A : Class) : (nb070_alpha_dummy_028 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0056 (A : Class) : (nb070_alpha_dummy_028 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_028, fv_syn_c1c] using (nb070_compact_fv_empty_0038 A)

theorem nb070_compact_fv_empty_0039 (x : Var) : (nb070_alpha_dummy_029 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0057 (x : Var) : (nb070_alpha_dummy_029 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_029, fv_syn_c1c] using (nb070_compact_fv_empty_0039 x)

theorem nb070_compact_envfresh_0003 (x : Var) (A : Class) (b : Var) : TEnvFresh [((nb070_alpha_dummy_040 A), (nb070_alpha_dummy_043 x)), ((nb070_alpha_dummy_039 A), (nb070_alpha_dummy_042 x)), ((nb070_alpha_dummy_038 A), (nb070_alpha_dummy_041 x)), ((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)), ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)), ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)), ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)), ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)), ((nb070_alpha_dummy_030 A), (nb070_alpha_dummy_031 x)), ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)), ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)), ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)), ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb070_alpha_dummy_040 A) (nb070_alpha_dummy_043 x) (nb070_wpp_notmem_0038 A) (nb070_wpp_notmem_0039 x) (TEnvFresh.consFresh (nb070_alpha_dummy_039 A) (nb070_alpha_dummy_042 x) (nb070_wpp_notmem_0040 A) (nb070_wpp_notmem_0041 x) (TEnvFresh.consFresh (nb070_alpha_dummy_038 A) (nb070_alpha_dummy_041 x) (nb070_wpp_notmem_0042 A) (nb070_wpp_notmem_0043 x) (TEnvFresh.consFresh (nb070_alpha_dummy_036 A) (nb070_alpha_dummy_037 x) (nb070_wpp_notmem_0044 A) (nb070_wpp_notmem_0045 x) (TEnvFresh.consFresh (nb070_alpha_dummy_032 A) (nb070_alpha_dummy_034 x) (nb070_wpp_notmem_0046 A) (nb070_wpp_notmem_0047 x) (TEnvFresh.consFresh (nb070_alpha_dummy_033 A) (nb070_alpha_dummy_035 x) (nb070_wpp_notmem_0048 A) (nb070_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb070_alpha_dummy_025 A) (nb070_alpha_dummy_027 x) (nb070_wpp_notmem_0050 A) (nb070_wpp_notmem_0051 x) (TEnvFresh.consFresh (nb070_alpha_dummy_024 A) (nb070_alpha_dummy_026 x) (nb070_wpp_notmem_0052 A) (nb070_wpp_notmem_0053 x) (TEnvFresh.consFresh (nb070_alpha_dummy_030 A) (nb070_alpha_dummy_031 x) (nb070_wpp_notmem_0054 A) (nb070_wpp_notmem_0055 x) (TEnvFresh.consFresh (nb070_alpha_dummy_028 A) (nb070_alpha_dummy_029 x) (nb070_wpp_notmem_0056 A) (nb070_wpp_notmem_0057 x) (TEnvFresh.consFresh (nb070_alpha_dummy_009 A) (nb070_alpha_dummy_011 x) (nb070_wpp_notmem_0024 A) (nb070_wpp_notmem_0025 x) (TEnvFresh.consFresh (nb070_alpha_dummy_008 A) (nb070_alpha_dummy_010 x) (nb070_wpp_notmem_0026 A) (nb070_wpp_notmem_0027 x) (TEnvFresh.consFresh (nb070_alpha_dummy_001 A) x (nb070_wpp_notmem_0028 A) (nb070_wpp_notmem_0029 x) (TEnvFresh.consFresh (nb070_alpha_dummy_000 A) b (nb070_wpp_notmem_0030 A) (nb070_wpp_notmem_0031 b) (TEnvFresh.consFresh (nb070_alpha_dummy_002 A) (nb070_alpha_dummy_003 x A b) (nb070_wpp_notmem_0032 A) (nb070_wpp_notmem_0033 x A b) (TEnvFresh.consFresh (nb070_alpha_dummy_005 A) (nb070_alpha_dummy_007 x A b) (nb070_wpp_notmem_0034 A) (nb070_wpp_notmem_0035 x A b) (TEnvFresh.consFresh (nb070_alpha_dummy_004 A) (nb070_alpha_dummy_006 x A b) (nb070_wpp_notmem_0036 A) (nb070_wpp_notmem_0037 x A b) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))

noncomputable def nb070_wpp_refl_0003 (x : Var) (A : Class) (b : Var) : TReflOn [((nb070_alpha_dummy_040 A), (nb070_alpha_dummy_043 x)), ((nb070_alpha_dummy_039 A), (nb070_alpha_dummy_042 x)), ((nb070_alpha_dummy_038 A), (nb070_alpha_dummy_041 x)), ((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)), ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)), ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)), ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)), ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)), ((nb070_alpha_dummy_030 A), (nb070_alpha_dummy_031 x)), ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)), ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)), ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)), ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb070_compact_envfresh_0003 x A b)

theorem nb070_wpp_notmem_0058 (A : Class) : (nb070_alpha_dummy_040 A) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_040, fv_syn_c0] using (nb070_compact_fv_empty_0020 A)

theorem nb070_wpp_notmem_0059 (x : Var) : (nb070_alpha_dummy_043 x) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_043, fv_syn_c0] using (nb070_compact_fv_empty_0021 x)

theorem nb070_wpp_notmem_0060 (A : Class) : (nb070_alpha_dummy_039 A) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_039, fv_syn_c0] using (nb070_compact_fv_empty_0022 A)

theorem nb070_wpp_notmem_0061 (x : Var) : (nb070_alpha_dummy_042 x) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_042, fv_syn_c0] using (nb070_compact_fv_empty_0023 x)

theorem nb070_wpp_notmem_0062 (A : Class) : (nb070_alpha_dummy_038 A) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_038, fv_syn_c0] using (nb070_compact_fv_empty_0024 A)

theorem nb070_wpp_notmem_0063 (x : Var) : (nb070_alpha_dummy_041 x) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_041, fv_syn_c0] using (nb070_compact_fv_empty_0025 x)

theorem nb070_wpp_notmem_0064 (A : Class) : (nb070_alpha_dummy_036 A) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_036, fv_syn_c0] using (nb070_compact_fv_empty_0026 A)

theorem nb070_wpp_notmem_0065 (x : Var) : (nb070_alpha_dummy_037 x) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_037, fv_syn_c0] using (nb070_compact_fv_empty_0027 x)

theorem nb070_wpp_notmem_0066 (A : Class) : (nb070_alpha_dummy_032 A) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_032, fv_syn_c0] using (nb070_compact_fv_empty_0028 A)

theorem nb070_wpp_notmem_0067 (x : Var) : (nb070_alpha_dummy_034 x) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_034, fv_syn_c0] using (nb070_compact_fv_empty_0029 x)

theorem nb070_wpp_notmem_0068 (A : Class) : (nb070_alpha_dummy_033 A) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_033, fv_syn_c0] using (nb070_compact_fv_empty_0030 A)

theorem nb070_wpp_notmem_0069 (x : Var) : (nb070_alpha_dummy_035 x) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_035, fv_syn_c0] using (nb070_compact_fv_empty_0031 x)

theorem nb070_wpp_notmem_0070 (A : Class) : (nb070_alpha_dummy_025 A) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_025, fv_syn_c0] using (nb070_compact_fv_empty_0032 A)

theorem nb070_wpp_notmem_0071 (x : Var) : (nb070_alpha_dummy_027 x) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_027, fv_syn_c0] using (nb070_compact_fv_empty_0033 x)

theorem nb070_wpp_notmem_0072 (A : Class) : (nb070_alpha_dummy_024 A) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_024, fv_syn_c0] using (nb070_compact_fv_empty_0034 A)

theorem nb070_wpp_notmem_0073 (x : Var) : (nb070_alpha_dummy_026 x) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_026, fv_syn_c0] using (nb070_compact_fv_empty_0035 x)

theorem nb070_wpp_notmem_0074 (A : Class) : (nb070_alpha_dummy_030 A) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_030, fv_syn_c0] using (nb070_compact_fv_empty_0036 A)

theorem nb070_wpp_notmem_0075 (x : Var) : (nb070_alpha_dummy_031 x) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_031, fv_syn_c0] using (nb070_compact_fv_empty_0037 x)

theorem nb070_wpp_notmem_0076 (A : Class) : (nb070_alpha_dummy_028 A) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_028, fv_syn_c0] using (nb070_compact_fv_empty_0038 A)

theorem nb070_wpp_notmem_0077 (x : Var) : (nb070_alpha_dummy_029 x) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_029, fv_syn_c0] using (nb070_compact_fv_empty_0039 x)

theorem nb070_wpp_notmem_0078 (A : Class) : (nb070_alpha_dummy_009 A) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_009, fv_syn_c0] using (nb070_compact_fv_empty_0014 A)

theorem nb070_wpp_notmem_0079 (x : Var) : (nb070_alpha_dummy_011 x) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_011, fv_syn_c0] using (nb070_compact_fv_empty_0015 x)

theorem nb070_wpp_notmem_0080 (A : Class) : (nb070_alpha_dummy_008 A) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_008, fv_syn_c0] using (nb070_compact_fv_empty_0016 A)

theorem nb070_wpp_notmem_0081 (x : Var) : (nb070_alpha_dummy_010 x) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_010, fv_syn_c0] using (nb070_compact_fv_empty_0017 x)

theorem nb070_wpp_notmem_0082 (A : Class) : (nb070_alpha_dummy_001 A) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_001, fv_syn_c0] using (nb070_compact_fv_empty_0018 A)

theorem nb070_wpp_notmem_0083 (x : Var) : x ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb070_compact_fv_empty_0019 x)

theorem nb070_wpp_notmem_0084 (A : Class) : (nb070_alpha_dummy_000 A) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_000, fv_syn_c0] using (nb070_compact_fv_empty_0000 A)

theorem nb070_wpp_notmem_0085 (b : Var) : b ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb070_compact_fv_empty_0001 b)

theorem nb070_wpp_notmem_0086 (A : Class) : (nb070_alpha_dummy_002 A) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_002, fv_syn_c0] using (nb070_compact_fv_empty_0002 A)

theorem nb070_wpp_notmem_0087 (x : Var) (A : Class) (b : Var) : (nb070_alpha_dummy_003 x A b) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_003, fv_syn_c0] using (nb070_compact_fv_empty_0003 x A b)

theorem nb070_wpp_notmem_0088 (A : Class) : (nb070_alpha_dummy_005 A) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_005, fv_syn_c0] using (nb070_compact_fv_empty_0004 A)

theorem nb070_wpp_notmem_0089 (x : Var) (A : Class) (b : Var) : (nb070_alpha_dummy_007 x A b) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_007, fv_syn_c0] using (nb070_compact_fv_empty_0005 x A b)

theorem nb070_wpp_notmem_0090 (A : Class) : (nb070_alpha_dummy_004 A) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_004, fv_syn_c0] using (nb070_compact_fv_empty_0006 A)

theorem nb070_wpp_notmem_0091 (x : Var) (A : Class) (b : Var) : (nb070_alpha_dummy_006 x A b) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_006, fv_syn_c0] using (nb070_compact_fv_empty_0007 x A b)

theorem nb070_compact_envfresh_0004 (x : Var) (A : Class) (b : Var) : TEnvFresh [((nb070_alpha_dummy_040 A), (nb070_alpha_dummy_043 x)), ((nb070_alpha_dummy_039 A), (nb070_alpha_dummy_042 x)), ((nb070_alpha_dummy_038 A), (nb070_alpha_dummy_041 x)), ((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)), ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)), ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)), ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)), ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)), ((nb070_alpha_dummy_030 A), (nb070_alpha_dummy_031 x)), ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)), ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)), ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)), ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb070_alpha_dummy_040 A) (nb070_alpha_dummy_043 x) (nb070_wpp_notmem_0058 A) (nb070_wpp_notmem_0059 x) (TEnvFresh.consFresh (nb070_alpha_dummy_039 A) (nb070_alpha_dummy_042 x) (nb070_wpp_notmem_0060 A) (nb070_wpp_notmem_0061 x) (TEnvFresh.consFresh (nb070_alpha_dummy_038 A) (nb070_alpha_dummy_041 x) (nb070_wpp_notmem_0062 A) (nb070_wpp_notmem_0063 x) (TEnvFresh.consFresh (nb070_alpha_dummy_036 A) (nb070_alpha_dummy_037 x) (nb070_wpp_notmem_0064 A) (nb070_wpp_notmem_0065 x) (TEnvFresh.consFresh (nb070_alpha_dummy_032 A) (nb070_alpha_dummy_034 x) (nb070_wpp_notmem_0066 A) (nb070_wpp_notmem_0067 x) (TEnvFresh.consFresh (nb070_alpha_dummy_033 A) (nb070_alpha_dummy_035 x) (nb070_wpp_notmem_0068 A) (nb070_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb070_alpha_dummy_025 A) (nb070_alpha_dummy_027 x) (nb070_wpp_notmem_0070 A) (nb070_wpp_notmem_0071 x) (TEnvFresh.consFresh (nb070_alpha_dummy_024 A) (nb070_alpha_dummy_026 x) (nb070_wpp_notmem_0072 A) (nb070_wpp_notmem_0073 x) (TEnvFresh.consFresh (nb070_alpha_dummy_030 A) (nb070_alpha_dummy_031 x) (nb070_wpp_notmem_0074 A) (nb070_wpp_notmem_0075 x) (TEnvFresh.consFresh (nb070_alpha_dummy_028 A) (nb070_alpha_dummy_029 x) (nb070_wpp_notmem_0076 A) (nb070_wpp_notmem_0077 x) (TEnvFresh.consFresh (nb070_alpha_dummy_009 A) (nb070_alpha_dummy_011 x) (nb070_wpp_notmem_0078 A) (nb070_wpp_notmem_0079 x) (TEnvFresh.consFresh (nb070_alpha_dummy_008 A) (nb070_alpha_dummy_010 x) (nb070_wpp_notmem_0080 A) (nb070_wpp_notmem_0081 x) (TEnvFresh.consFresh (nb070_alpha_dummy_001 A) x (nb070_wpp_notmem_0082 A) (nb070_wpp_notmem_0083 x) (TEnvFresh.consFresh (nb070_alpha_dummy_000 A) b (nb070_wpp_notmem_0084 A) (nb070_wpp_notmem_0085 b) (TEnvFresh.consFresh (nb070_alpha_dummy_002 A) (nb070_alpha_dummy_003 x A b) (nb070_wpp_notmem_0086 A) (nb070_wpp_notmem_0087 x A b) (TEnvFresh.consFresh (nb070_alpha_dummy_005 A) (nb070_alpha_dummy_007 x A b) (nb070_wpp_notmem_0088 A) (nb070_wpp_notmem_0089 x A b) (TEnvFresh.consFresh (nb070_alpha_dummy_004 A) (nb070_alpha_dummy_006 x A b) (nb070_wpp_notmem_0090 A) (nb070_wpp_notmem_0091 x A b) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))

noncomputable def nb070_wpp_refl_0004 (x : Var) (A : Class) (b : Var) : TReflOn [((nb070_alpha_dummy_040 A), (nb070_alpha_dummy_043 x)), ((nb070_alpha_dummy_039 A), (nb070_alpha_dummy_042 x)), ((nb070_alpha_dummy_038 A), (nb070_alpha_dummy_041 x)), ((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)), ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)), ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)), ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)), ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)), ((nb070_alpha_dummy_030 A), (nb070_alpha_dummy_031 x)), ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)), ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)), ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)), ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb070_compact_envfresh_0004 x A b)

noncomputable def nb070_split_alpha_0001 (x : Var) (A : Class) (b : Var) : TAlphaWff [((nb070_alpha_dummy_040 A), (nb070_alpha_dummy_043 x)), ((nb070_alpha_dummy_039 A), (nb070_alpha_dummy_042 x)), ((nb070_alpha_dummy_038 A), (nb070_alpha_dummy_041 x)), ((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)), ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)), ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)), ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)), ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)), ((nb070_alpha_dummy_030 A), (nb070_alpha_dummy_031 x)), ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)), ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)), ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)), ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb070_alpha_dummy_039 A)) (Class.cv (nb070_alpha_dummy_040 A))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb070_alpha_dummy_038 A)) (syn_cun (Class.cv (nb070_alpha_dummy_039 A)) (Class.cv (nb070_alpha_dummy_040 A)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb070_alpha_dummy_042 x)) (Class.cv (nb070_alpha_dummy_043 x))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb070_alpha_dummy_041 x)) (syn_cun (Class.cv (nb070_alpha_dummy_042 x)) (Class.cv (nb070_alpha_dummy_043 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0032 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0033 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0030 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0031 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0036 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0037 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0034 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0035 x) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0032 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0033 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0030 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0031 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0036 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0037 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0034 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0035 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb070_alpha_dummy_040 A), (nb070_alpha_dummy_043 x)), ((nb070_alpha_dummy_039 A), (nb070_alpha_dummy_042 x)), ((nb070_alpha_dummy_038 A), (nb070_alpha_dummy_041 x)), ((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)), ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)), ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)), ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)), ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)), ((nb070_alpha_dummy_030 A), (nb070_alpha_dummy_031 x)), ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)), ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)), ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)), ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] (syn_c0) (nb070_wpp_refl_0004 x A b))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0040 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0041 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0038 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0039 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0040 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0041 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0038 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0039 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0044 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0045 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0042 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0043 x) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0044 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0045 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0042 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0043 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb070_wpp_notmem_0092 (A : Class) : (nb070_alpha_dummy_036 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_036, fv_syn_cnnc] using (nb070_compact_fv_empty_0026 A)

theorem nb070_wpp_notmem_0093 (x : Var) : (nb070_alpha_dummy_037 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_037, fv_syn_cnnc] using (nb070_compact_fv_empty_0027 x)

theorem nb070_wpp_notmem_0094 (A : Class) : (nb070_alpha_dummy_032 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_032, fv_syn_cnnc] using (nb070_compact_fv_empty_0028 A)

theorem nb070_wpp_notmem_0095 (x : Var) : (nb070_alpha_dummy_034 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_034, fv_syn_cnnc] using (nb070_compact_fv_empty_0029 x)

theorem nb070_wpp_notmem_0096 (A : Class) : (nb070_alpha_dummy_033 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_033, fv_syn_cnnc] using (nb070_compact_fv_empty_0030 A)

theorem nb070_wpp_notmem_0097 (x : Var) : (nb070_alpha_dummy_035 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_035, fv_syn_cnnc] using (nb070_compact_fv_empty_0031 x)

theorem nb070_wpp_notmem_0098 (A : Class) : (nb070_alpha_dummy_025 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_025, fv_syn_cnnc] using (nb070_compact_fv_empty_0032 A)

theorem nb070_wpp_notmem_0099 (x : Var) : (nb070_alpha_dummy_027 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_027, fv_syn_cnnc] using (nb070_compact_fv_empty_0033 x)

theorem nb070_wpp_notmem_0100 (A : Class) : (nb070_alpha_dummy_024 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_024, fv_syn_cnnc] using (nb070_compact_fv_empty_0034 A)

theorem nb070_wpp_notmem_0101 (x : Var) : (nb070_alpha_dummy_026 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_026, fv_syn_cnnc] using (nb070_compact_fv_empty_0035 x)

theorem nb070_wpp_notmem_0102 (A : Class) : (nb070_alpha_dummy_030 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_030, fv_syn_cnnc] using (nb070_compact_fv_empty_0036 A)

theorem nb070_wpp_notmem_0103 (x : Var) : (nb070_alpha_dummy_031 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_031, fv_syn_cnnc] using (nb070_compact_fv_empty_0037 x)

theorem nb070_wpp_notmem_0104 (A : Class) : (nb070_alpha_dummy_028 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_028, fv_syn_cnnc] using (nb070_compact_fv_empty_0038 A)

theorem nb070_wpp_notmem_0105 (x : Var) : (nb070_alpha_dummy_029 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_029, fv_syn_cnnc] using (nb070_compact_fv_empty_0039 x)

theorem nb070_wpp_notmem_0106 (A : Class) : (nb070_alpha_dummy_009 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_009, fv_syn_cnnc] using (nb070_compact_fv_empty_0014 A)

theorem nb070_wpp_notmem_0107 (x : Var) : (nb070_alpha_dummy_011 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_011, fv_syn_cnnc] using (nb070_compact_fv_empty_0015 x)

theorem nb070_wpp_notmem_0108 (A : Class) : (nb070_alpha_dummy_008 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_008, fv_syn_cnnc] using (nb070_compact_fv_empty_0016 A)

theorem nb070_wpp_notmem_0109 (x : Var) : (nb070_alpha_dummy_010 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_010, fv_syn_cnnc] using (nb070_compact_fv_empty_0017 x)

theorem nb070_wpp_notmem_0110 (A : Class) : (nb070_alpha_dummy_001 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_001, fv_syn_cnnc] using (nb070_compact_fv_empty_0018 A)

theorem nb070_wpp_notmem_0111 (x : Var) : x ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb070_compact_fv_empty_0019 x)

theorem nb070_wpp_notmem_0112 (A : Class) : (nb070_alpha_dummy_000 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_000, fv_syn_cnnc] using (nb070_compact_fv_empty_0000 A)

theorem nb070_wpp_notmem_0113 (b : Var) : b ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb070_compact_fv_empty_0001 b)

theorem nb070_wpp_notmem_0114 (A : Class) : (nb070_alpha_dummy_002 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_002, fv_syn_cnnc] using (nb070_compact_fv_empty_0002 A)

theorem nb070_wpp_notmem_0115 (x : Var) (A : Class) (b : Var) : (nb070_alpha_dummy_003 x A b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_003, fv_syn_cnnc] using (nb070_compact_fv_empty_0003 x A b)

theorem nb070_wpp_notmem_0116 (A : Class) : (nb070_alpha_dummy_005 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_005, fv_syn_cnnc] using (nb070_compact_fv_empty_0004 A)

theorem nb070_wpp_notmem_0117 (x : Var) (A : Class) (b : Var) : (nb070_alpha_dummy_007 x A b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_007, fv_syn_cnnc] using (nb070_compact_fv_empty_0005 x A b)

theorem nb070_wpp_notmem_0118 (A : Class) : (nb070_alpha_dummy_004 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_004, fv_syn_cnnc] using (nb070_compact_fv_empty_0006 A)

theorem nb070_wpp_notmem_0119 (x : Var) (A : Class) (b : Var) : (nb070_alpha_dummy_006 x A b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_006, fv_syn_cnnc] using (nb070_compact_fv_empty_0007 x A b)

theorem nb070_compact_envfresh_0005 (x : Var) (A : Class) (b : Var) : TEnvFresh [((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)), ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)), ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)), ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)), ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)), ((nb070_alpha_dummy_030 A), (nb070_alpha_dummy_031 x)), ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)), ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)), ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)), ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb070_alpha_dummy_036 A) (nb070_alpha_dummy_037 x) (nb070_wpp_notmem_0092 A) (nb070_wpp_notmem_0093 x) (TEnvFresh.consFresh (nb070_alpha_dummy_032 A) (nb070_alpha_dummy_034 x) (nb070_wpp_notmem_0094 A) (nb070_wpp_notmem_0095 x) (TEnvFresh.consFresh (nb070_alpha_dummy_033 A) (nb070_alpha_dummy_035 x) (nb070_wpp_notmem_0096 A) (nb070_wpp_notmem_0097 x) (TEnvFresh.consFresh (nb070_alpha_dummy_025 A) (nb070_alpha_dummy_027 x) (nb070_wpp_notmem_0098 A) (nb070_wpp_notmem_0099 x) (TEnvFresh.consFresh (nb070_alpha_dummy_024 A) (nb070_alpha_dummy_026 x) (nb070_wpp_notmem_0100 A) (nb070_wpp_notmem_0101 x) (TEnvFresh.consFresh (nb070_alpha_dummy_030 A) (nb070_alpha_dummy_031 x) (nb070_wpp_notmem_0102 A) (nb070_wpp_notmem_0103 x) (TEnvFresh.consFresh (nb070_alpha_dummy_028 A) (nb070_alpha_dummy_029 x) (nb070_wpp_notmem_0104 A) (nb070_wpp_notmem_0105 x) (TEnvFresh.consFresh (nb070_alpha_dummy_009 A) (nb070_alpha_dummy_011 x) (nb070_wpp_notmem_0106 A) (nb070_wpp_notmem_0107 x) (TEnvFresh.consFresh (nb070_alpha_dummy_008 A) (nb070_alpha_dummy_010 x) (nb070_wpp_notmem_0108 A) (nb070_wpp_notmem_0109 x) (TEnvFresh.consFresh (nb070_alpha_dummy_001 A) x (nb070_wpp_notmem_0110 A) (nb070_wpp_notmem_0111 x) (TEnvFresh.consFresh (nb070_alpha_dummy_000 A) b (nb070_wpp_notmem_0112 A) (nb070_wpp_notmem_0113 b) (TEnvFresh.consFresh (nb070_alpha_dummy_002 A) (nb070_alpha_dummy_003 x A b) (nb070_wpp_notmem_0114 A) (nb070_wpp_notmem_0115 x A b) (TEnvFresh.consFresh (nb070_alpha_dummy_005 A) (nb070_alpha_dummy_007 x A b) (nb070_wpp_notmem_0116 A) (nb070_wpp_notmem_0117 x A b) (TEnvFresh.consFresh (nb070_alpha_dummy_004 A) (nb070_alpha_dummy_006 x A b) (nb070_wpp_notmem_0118 A) (nb070_wpp_notmem_0119 x A b) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))

noncomputable def nb070_wpp_refl_0005 (x : Var) (A : Class) (b : Var) : TReflOn [((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)), ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)), ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)), ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)), ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)), ((nb070_alpha_dummy_030 A), (nb070_alpha_dummy_031 x)), ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)), ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)), ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)), ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb070_compact_envfresh_0005 x A b)

noncomputable def nb070_split_alpha_0002 (x : Var) (A : Class) (b : Var) : TAlphaWff [((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)), ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)), ((nb070_alpha_dummy_030 A), (nb070_alpha_dummy_031 x)), ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)), ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)), ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)), ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A)) (syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))) (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x)) (syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb070_alpha_dummy_009 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_008 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb070_alpha_dummy_011 x))).fv ∪ ((Class.cv (nb070_alpha_dummy_010 x))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0024 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0025 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0024 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0025 x) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb070_alpha_dummy_025 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb070_alpha_dummy_027 x))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0028 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0029 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0028 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0029 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0026 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0027 x) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb070_alpha_dummy_040 A), (nb070_alpha_dummy_043 x)), ((nb070_alpha_dummy_039 A), (nb070_alpha_dummy_042 x)), ((nb070_alpha_dummy_038 A), (nb070_alpha_dummy_041 x)), ((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)), ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)), ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)), ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)), ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)), ((nb070_alpha_dummy_030 A), (nb070_alpha_dummy_031 x)), ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)), ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)), ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)), ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] (syn_c1c) (nb070_wpp_refl_0003 x A b))) (TAlphaWff.neg (TAlphaWff.neg (nb070_split_alpha_0001 x A b)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0026 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0027 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)), ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)), ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)), ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)), ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)), ((nb070_alpha_dummy_030 A), (nb070_alpha_dummy_031 x)), ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)), ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)), ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)), ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] (syn_cnnc) (nb070_wpp_refl_0005 x A b))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0026 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0027 x) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0026 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0027 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)), ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)), ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)), ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)), ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)), ((nb070_alpha_dummy_030 A), (nb070_alpha_dummy_031 x)), ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)), ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)), ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)), ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] (syn_cnnc) (nb070_wpp_refl_0005 x A b))))))))))))))))))

theorem nb070_compact_fv_empty_0040 (A : Class) : (nb070_alpha_dummy_058 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0120 (A : Class) : (nb070_alpha_dummy_058 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_058, fv_syn_c1c] using (nb070_compact_fv_empty_0040 A)

theorem nb070_compact_fv_empty_0041 (x : Var) : (nb070_alpha_dummy_059 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0121 (x : Var) : (nb070_alpha_dummy_059 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_059, fv_syn_c1c] using (nb070_compact_fv_empty_0041 x)

theorem nb070_compact_fv_empty_0042 (A : Class) : (nb070_alpha_dummy_056 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0122 (A : Class) : (nb070_alpha_dummy_056 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_056, fv_syn_c1c] using (nb070_compact_fv_empty_0042 A)

theorem nb070_compact_fv_empty_0043 (x : Var) : (nb070_alpha_dummy_057 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0123 (x : Var) : (nb070_alpha_dummy_057 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_057, fv_syn_c1c] using (nb070_compact_fv_empty_0043 x)

theorem nb070_compact_fv_empty_0044 (A : Class) : (nb070_alpha_dummy_054 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0124 (A : Class) : (nb070_alpha_dummy_054 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_054, fv_syn_c1c] using (nb070_compact_fv_empty_0044 A)

theorem nb070_compact_fv_empty_0045 (x : Var) : (nb070_alpha_dummy_055 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0125 (x : Var) : (nb070_alpha_dummy_055 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_055, fv_syn_c1c] using (nb070_compact_fv_empty_0045 x)

theorem nb070_compact_envfresh_0006 (x : Var) (A : Class) (b : Var) : TEnvFresh [((nb070_alpha_dummy_040 A), (nb070_alpha_dummy_043 x)), ((nb070_alpha_dummy_039 A), (nb070_alpha_dummy_042 x)), ((nb070_alpha_dummy_038 A), (nb070_alpha_dummy_041 x)), ((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)), ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)), ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)), ((nb070_alpha_dummy_058 A), (nb070_alpha_dummy_059 x)), ((nb070_alpha_dummy_056 A), (nb070_alpha_dummy_057 x)), ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)), ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)), ((nb070_alpha_dummy_054 A), (nb070_alpha_dummy_055 x)), ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)), ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)), ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)), ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb070_alpha_dummy_040 A) (nb070_alpha_dummy_043 x) (nb070_wpp_notmem_0038 A) (nb070_wpp_notmem_0039 x) (TEnvFresh.consFresh (nb070_alpha_dummy_039 A) (nb070_alpha_dummy_042 x) (nb070_wpp_notmem_0040 A) (nb070_wpp_notmem_0041 x) (TEnvFresh.consFresh (nb070_alpha_dummy_038 A) (nb070_alpha_dummy_041 x) (nb070_wpp_notmem_0042 A) (nb070_wpp_notmem_0043 x) (TEnvFresh.consFresh (nb070_alpha_dummy_036 A) (nb070_alpha_dummy_037 x) (nb070_wpp_notmem_0044 A) (nb070_wpp_notmem_0045 x) (TEnvFresh.consFresh (nb070_alpha_dummy_032 A) (nb070_alpha_dummy_034 x) (nb070_wpp_notmem_0046 A) (nb070_wpp_notmem_0047 x) (TEnvFresh.consFresh (nb070_alpha_dummy_033 A) (nb070_alpha_dummy_035 x) (nb070_wpp_notmem_0048 A) (nb070_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb070_alpha_dummy_058 A) (nb070_alpha_dummy_059 x) (nb070_wpp_notmem_0120 A) (nb070_wpp_notmem_0121 x) (TEnvFresh.consFresh (nb070_alpha_dummy_056 A) (nb070_alpha_dummy_057 x) (nb070_wpp_notmem_0122 A) (nb070_wpp_notmem_0123 x) (TEnvFresh.consFresh (nb070_alpha_dummy_025 A) (nb070_alpha_dummy_027 x) (nb070_wpp_notmem_0050 A) (nb070_wpp_notmem_0051 x) (TEnvFresh.consFresh (nb070_alpha_dummy_024 A) (nb070_alpha_dummy_026 x) (nb070_wpp_notmem_0052 A) (nb070_wpp_notmem_0053 x) (TEnvFresh.consFresh (nb070_alpha_dummy_054 A) (nb070_alpha_dummy_055 x) (nb070_wpp_notmem_0124 A) (nb070_wpp_notmem_0125 x) (TEnvFresh.consFresh (nb070_alpha_dummy_028 A) (nb070_alpha_dummy_029 x) (nb070_wpp_notmem_0056 A) (nb070_wpp_notmem_0057 x) (TEnvFresh.consFresh (nb070_alpha_dummy_009 A) (nb070_alpha_dummy_011 x) (nb070_wpp_notmem_0024 A) (nb070_wpp_notmem_0025 x) (TEnvFresh.consFresh (nb070_alpha_dummy_008 A) (nb070_alpha_dummy_010 x) (nb070_wpp_notmem_0026 A) (nb070_wpp_notmem_0027 x) (TEnvFresh.consFresh (nb070_alpha_dummy_001 A) x (nb070_wpp_notmem_0028 A) (nb070_wpp_notmem_0029 x) (TEnvFresh.consFresh (nb070_alpha_dummy_000 A) b (nb070_wpp_notmem_0030 A) (nb070_wpp_notmem_0031 b) (TEnvFresh.consFresh (nb070_alpha_dummy_002 A) (nb070_alpha_dummy_003 x A b) (nb070_wpp_notmem_0032 A) (nb070_wpp_notmem_0033 x A b) (TEnvFresh.consFresh (nb070_alpha_dummy_005 A) (nb070_alpha_dummy_007 x A b) (nb070_wpp_notmem_0034 A) (nb070_wpp_notmem_0035 x A b) (TEnvFresh.consFresh (nb070_alpha_dummy_004 A) (nb070_alpha_dummy_006 x A b) (nb070_wpp_notmem_0036 A) (nb070_wpp_notmem_0037 x A b) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))

noncomputable def nb070_wpp_refl_0006 (x : Var) (A : Class) (b : Var) : TReflOn [((nb070_alpha_dummy_040 A), (nb070_alpha_dummy_043 x)), ((nb070_alpha_dummy_039 A), (nb070_alpha_dummy_042 x)), ((nb070_alpha_dummy_038 A), (nb070_alpha_dummy_041 x)), ((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)), ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)), ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)), ((nb070_alpha_dummy_058 A), (nb070_alpha_dummy_059 x)), ((nb070_alpha_dummy_056 A), (nb070_alpha_dummy_057 x)), ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)), ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)), ((nb070_alpha_dummy_054 A), (nb070_alpha_dummy_055 x)), ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)), ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)), ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)), ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb070_compact_envfresh_0006 x A b)

theorem nb070_wpp_notmem_0126 (A : Class) : (nb070_alpha_dummy_058 A) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_058, fv_syn_c0] using (nb070_compact_fv_empty_0040 A)

theorem nb070_wpp_notmem_0127 (x : Var) : (nb070_alpha_dummy_059 x) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_059, fv_syn_c0] using (nb070_compact_fv_empty_0041 x)

theorem nb070_wpp_notmem_0128 (A : Class) : (nb070_alpha_dummy_056 A) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_056, fv_syn_c0] using (nb070_compact_fv_empty_0042 A)

theorem nb070_wpp_notmem_0129 (x : Var) : (nb070_alpha_dummy_057 x) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_057, fv_syn_c0] using (nb070_compact_fv_empty_0043 x)

theorem nb070_wpp_notmem_0130 (A : Class) : (nb070_alpha_dummy_054 A) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_054, fv_syn_c0] using (nb070_compact_fv_empty_0044 A)

theorem nb070_wpp_notmem_0131 (x : Var) : (nb070_alpha_dummy_055 x) ∉ ((syn_c0)).fv := by
  simpa only [nb070_alpha_dummy_055, fv_syn_c0] using (nb070_compact_fv_empty_0045 x)

theorem nb070_compact_envfresh_0007 (x : Var) (A : Class) (b : Var) : TEnvFresh [((nb070_alpha_dummy_040 A), (nb070_alpha_dummy_043 x)), ((nb070_alpha_dummy_039 A), (nb070_alpha_dummy_042 x)), ((nb070_alpha_dummy_038 A), (nb070_alpha_dummy_041 x)), ((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)), ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)), ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)), ((nb070_alpha_dummy_058 A), (nb070_alpha_dummy_059 x)), ((nb070_alpha_dummy_056 A), (nb070_alpha_dummy_057 x)), ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)), ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)), ((nb070_alpha_dummy_054 A), (nb070_alpha_dummy_055 x)), ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)), ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)), ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)), ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb070_alpha_dummy_040 A) (nb070_alpha_dummy_043 x) (nb070_wpp_notmem_0058 A) (nb070_wpp_notmem_0059 x) (TEnvFresh.consFresh (nb070_alpha_dummy_039 A) (nb070_alpha_dummy_042 x) (nb070_wpp_notmem_0060 A) (nb070_wpp_notmem_0061 x) (TEnvFresh.consFresh (nb070_alpha_dummy_038 A) (nb070_alpha_dummy_041 x) (nb070_wpp_notmem_0062 A) (nb070_wpp_notmem_0063 x) (TEnvFresh.consFresh (nb070_alpha_dummy_036 A) (nb070_alpha_dummy_037 x) (nb070_wpp_notmem_0064 A) (nb070_wpp_notmem_0065 x) (TEnvFresh.consFresh (nb070_alpha_dummy_032 A) (nb070_alpha_dummy_034 x) (nb070_wpp_notmem_0066 A) (nb070_wpp_notmem_0067 x) (TEnvFresh.consFresh (nb070_alpha_dummy_033 A) (nb070_alpha_dummy_035 x) (nb070_wpp_notmem_0068 A) (nb070_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb070_alpha_dummy_058 A) (nb070_alpha_dummy_059 x) (nb070_wpp_notmem_0126 A) (nb070_wpp_notmem_0127 x) (TEnvFresh.consFresh (nb070_alpha_dummy_056 A) (nb070_alpha_dummy_057 x) (nb070_wpp_notmem_0128 A) (nb070_wpp_notmem_0129 x) (TEnvFresh.consFresh (nb070_alpha_dummy_025 A) (nb070_alpha_dummy_027 x) (nb070_wpp_notmem_0070 A) (nb070_wpp_notmem_0071 x) (TEnvFresh.consFresh (nb070_alpha_dummy_024 A) (nb070_alpha_dummy_026 x) (nb070_wpp_notmem_0072 A) (nb070_wpp_notmem_0073 x) (TEnvFresh.consFresh (nb070_alpha_dummy_054 A) (nb070_alpha_dummy_055 x) (nb070_wpp_notmem_0130 A) (nb070_wpp_notmem_0131 x) (TEnvFresh.consFresh (nb070_alpha_dummy_028 A) (nb070_alpha_dummy_029 x) (nb070_wpp_notmem_0076 A) (nb070_wpp_notmem_0077 x) (TEnvFresh.consFresh (nb070_alpha_dummy_009 A) (nb070_alpha_dummy_011 x) (nb070_wpp_notmem_0078 A) (nb070_wpp_notmem_0079 x) (TEnvFresh.consFresh (nb070_alpha_dummy_008 A) (nb070_alpha_dummy_010 x) (nb070_wpp_notmem_0080 A) (nb070_wpp_notmem_0081 x) (TEnvFresh.consFresh (nb070_alpha_dummy_001 A) x (nb070_wpp_notmem_0082 A) (nb070_wpp_notmem_0083 x) (TEnvFresh.consFresh (nb070_alpha_dummy_000 A) b (nb070_wpp_notmem_0084 A) (nb070_wpp_notmem_0085 b) (TEnvFresh.consFresh (nb070_alpha_dummy_002 A) (nb070_alpha_dummy_003 x A b) (nb070_wpp_notmem_0086 A) (nb070_wpp_notmem_0087 x A b) (TEnvFresh.consFresh (nb070_alpha_dummy_005 A) (nb070_alpha_dummy_007 x A b) (nb070_wpp_notmem_0088 A) (nb070_wpp_notmem_0089 x A b) (TEnvFresh.consFresh (nb070_alpha_dummy_004 A) (nb070_alpha_dummy_006 x A b) (nb070_wpp_notmem_0090 A) (nb070_wpp_notmem_0091 x A b) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))

noncomputable def nb070_wpp_refl_0007 (x : Var) (A : Class) (b : Var) : TReflOn [((nb070_alpha_dummy_040 A), (nb070_alpha_dummy_043 x)), ((nb070_alpha_dummy_039 A), (nb070_alpha_dummy_042 x)), ((nb070_alpha_dummy_038 A), (nb070_alpha_dummy_041 x)), ((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)), ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)), ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)), ((nb070_alpha_dummy_058 A), (nb070_alpha_dummy_059 x)), ((nb070_alpha_dummy_056 A), (nb070_alpha_dummy_057 x)), ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)), ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)), ((nb070_alpha_dummy_054 A), (nb070_alpha_dummy_055 x)), ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)), ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)), ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)), ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb070_compact_envfresh_0007 x A b)

noncomputable def nb070_split_alpha_0003 (x : Var) (A : Class) (b : Var) : TAlphaWff [((nb070_alpha_dummy_040 A), (nb070_alpha_dummy_043 x)), ((nb070_alpha_dummy_039 A), (nb070_alpha_dummy_042 x)), ((nb070_alpha_dummy_038 A), (nb070_alpha_dummy_041 x)), ((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)), ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)), ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)), ((nb070_alpha_dummy_058 A), (nb070_alpha_dummy_059 x)), ((nb070_alpha_dummy_056 A), (nb070_alpha_dummy_057 x)), ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)), ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)), ((nb070_alpha_dummy_054 A), (nb070_alpha_dummy_055 x)), ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)), ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)), ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)), ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb070_alpha_dummy_039 A)) (Class.cv (nb070_alpha_dummy_040 A))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb070_alpha_dummy_038 A)) (syn_cun (Class.cv (nb070_alpha_dummy_039 A)) (Class.cv (nb070_alpha_dummy_040 A)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb070_alpha_dummy_042 x)) (Class.cv (nb070_alpha_dummy_043 x))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb070_alpha_dummy_041 x)) (syn_cun (Class.cv (nb070_alpha_dummy_042 x)) (Class.cv (nb070_alpha_dummy_043 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0032 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0033 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0030 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0031 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0036 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0037 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0034 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0035 x) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0032 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0033 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0030 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0031 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0036 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0037 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0034 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0035 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb070_alpha_dummy_040 A), (nb070_alpha_dummy_043 x)), ((nb070_alpha_dummy_039 A), (nb070_alpha_dummy_042 x)), ((nb070_alpha_dummy_038 A), (nb070_alpha_dummy_041 x)), ((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)), ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)), ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)), ((nb070_alpha_dummy_058 A), (nb070_alpha_dummy_059 x)), ((nb070_alpha_dummy_056 A), (nb070_alpha_dummy_057 x)), ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)), ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)), ((nb070_alpha_dummy_054 A), (nb070_alpha_dummy_055 x)), ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)), ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)), ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)), ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] (syn_c0) (nb070_wpp_refl_0007 x A b))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0040 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0041 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0038 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0039 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0040 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0041 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0038 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0039 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0044 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0045 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0042 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0043 x) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0044 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0045 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0042 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0043 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb070_wpp_notmem_0132 (A : Class) : (nb070_alpha_dummy_058 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_058, fv_syn_cnnc] using (nb070_compact_fv_empty_0040 A)

theorem nb070_wpp_notmem_0133 (x : Var) : (nb070_alpha_dummy_059 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_059, fv_syn_cnnc] using (nb070_compact_fv_empty_0041 x)

theorem nb070_wpp_notmem_0134 (A : Class) : (nb070_alpha_dummy_056 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_056, fv_syn_cnnc] using (nb070_compact_fv_empty_0042 A)

theorem nb070_wpp_notmem_0135 (x : Var) : (nb070_alpha_dummy_057 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_057, fv_syn_cnnc] using (nb070_compact_fv_empty_0043 x)

theorem nb070_wpp_notmem_0136 (A : Class) : (nb070_alpha_dummy_054 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb070_alpha_dummy_054, fv_syn_cnnc] using (nb070_compact_fv_empty_0044 A)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
