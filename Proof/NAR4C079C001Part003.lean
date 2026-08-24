import NAR4C079C001Part002

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

noncomputable def nb079_wpp_refl_0002 (x : Var) (y : Var) (z : Var) (A : Class) : TReflOn [((nb079_alpha_dummy_035 A), (nb079_alpha_dummy_036 x y)), ((nb079_alpha_dummy_031 A), (nb079_alpha_dummy_033 x y)), ((nb079_alpha_dummy_032 A), (nb079_alpha_dummy_034 x y)), ((nb079_alpha_dummy_024 A), (nb079_alpha_dummy_026 x y)), ((nb079_alpha_dummy_023 A), (nb079_alpha_dummy_025 x y)), ((nb079_alpha_dummy_029 A), (nb079_alpha_dummy_030 x y)), ((nb079_alpha_dummy_027 A), (nb079_alpha_dummy_028 x y)), ((nb079_alpha_dummy_001 A), y), ((nb079_alpha_dummy_000 A), x), ((nb079_alpha_dummy_002 A), z)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb079_compact_envfresh_0002 x y z A)

theorem nb079_compact_fv_empty_0026 (A : Class) : (nb079_alpha_dummy_057 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0072 (A : Class) : (nb079_alpha_dummy_057 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_057, fv_syn_c1c] using (nb079_compact_fv_empty_0026 A)

theorem nb079_compact_fv_empty_0027 (x : Var) (y : Var) : (nb079_alpha_dummy_058 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0073 (x : Var) (y : Var) : (nb079_alpha_dummy_058 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_058, fv_syn_c1c] using (nb079_compact_fv_empty_0027 x y)

theorem nb079_compact_fv_empty_0028 (A : Class) : (nb079_alpha_dummy_055 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0074 (A : Class) : (nb079_alpha_dummy_055 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_055, fv_syn_c1c] using (nb079_compact_fv_empty_0028 A)

theorem nb079_compact_fv_empty_0029 (x : Var) (y : Var) : (nb079_alpha_dummy_056 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0075 (x : Var) (y : Var) : (nb079_alpha_dummy_056 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_056, fv_syn_c1c] using (nb079_compact_fv_empty_0029 x y)

theorem nb079_compact_fv_empty_0030 (A : Class) : (nb079_alpha_dummy_053 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0076 (A : Class) : (nb079_alpha_dummy_053 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_053, fv_syn_c1c] using (nb079_compact_fv_empty_0030 A)

theorem nb079_compact_fv_empty_0031 (x : Var) (y : Var) : (nb079_alpha_dummy_054 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0077 (x : Var) (y : Var) : (nb079_alpha_dummy_054 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_054, fv_syn_c1c] using (nb079_compact_fv_empty_0031 x y)

theorem nb079_compact_envfresh_0003 (x : Var) (y : Var) (z : Var) (A : Class) : TEnvFresh [((nb079_alpha_dummy_039 A), (nb079_alpha_dummy_042 x y)), ((nb079_alpha_dummy_038 A), (nb079_alpha_dummy_041 x y)), ((nb079_alpha_dummy_037 A), (nb079_alpha_dummy_040 x y)), ((nb079_alpha_dummy_035 A), (nb079_alpha_dummy_036 x y)), ((nb079_alpha_dummy_031 A), (nb079_alpha_dummy_033 x y)), ((nb079_alpha_dummy_032 A), (nb079_alpha_dummy_034 x y)), ((nb079_alpha_dummy_057 A), (nb079_alpha_dummy_058 x y)), ((nb079_alpha_dummy_055 A), (nb079_alpha_dummy_056 x y)), ((nb079_alpha_dummy_024 A), (nb079_alpha_dummy_026 x y)), ((nb079_alpha_dummy_023 A), (nb079_alpha_dummy_025 x y)), ((nb079_alpha_dummy_053 A), (nb079_alpha_dummy_054 x y)), ((nb079_alpha_dummy_027 A), (nb079_alpha_dummy_028 x y)), ((nb079_alpha_dummy_001 A), y), ((nb079_alpha_dummy_000 A), x), ((nb079_alpha_dummy_002 A), z)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb079_alpha_dummy_039 A) (nb079_alpha_dummy_042 x y) (nb079_wpp_notmem_0000 A) (nb079_wpp_notmem_0001 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_038 A) (nb079_alpha_dummy_041 x y) (nb079_wpp_notmem_0002 A) (nb079_wpp_notmem_0003 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_037 A) (nb079_alpha_dummy_040 x y) (nb079_wpp_notmem_0004 A) (nb079_wpp_notmem_0005 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_035 A) (nb079_alpha_dummy_036 x y) (nb079_wpp_notmem_0006 A) (nb079_wpp_notmem_0007 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_031 A) (nb079_alpha_dummy_033 x y) (nb079_wpp_notmem_0008 A) (nb079_wpp_notmem_0009 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_032 A) (nb079_alpha_dummy_034 x y) (nb079_wpp_notmem_0010 A) (nb079_wpp_notmem_0011 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_057 A) (nb079_alpha_dummy_058 x y) (nb079_wpp_notmem_0072 A) (nb079_wpp_notmem_0073 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_055 A) (nb079_alpha_dummy_056 x y) (nb079_wpp_notmem_0074 A) (nb079_wpp_notmem_0075 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_024 A) (nb079_alpha_dummy_026 x y) (nb079_wpp_notmem_0012 A) (nb079_wpp_notmem_0013 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_023 A) (nb079_alpha_dummy_025 x y) (nb079_wpp_notmem_0014 A) (nb079_wpp_notmem_0015 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_053 A) (nb079_alpha_dummy_054 x y) (nb079_wpp_notmem_0076 A) (nb079_wpp_notmem_0077 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_027 A) (nb079_alpha_dummy_028 x y) (nb079_wpp_notmem_0018 A) (nb079_wpp_notmem_0019 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_001 A) y (nb079_wpp_notmem_0020 A) (nb079_wpp_notmem_0021 y) (TEnvFresh.consFresh (nb079_alpha_dummy_000 A) x (nb079_wpp_notmem_0022 A) (nb079_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb079_alpha_dummy_002 A) z (nb079_wpp_notmem_0024 A) (nb079_wpp_notmem_0025 z) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb079_wpp_refl_0003 (x : Var) (y : Var) (z : Var) (A : Class) : TReflOn [((nb079_alpha_dummy_039 A), (nb079_alpha_dummy_042 x y)), ((nb079_alpha_dummy_038 A), (nb079_alpha_dummy_041 x y)), ((nb079_alpha_dummy_037 A), (nb079_alpha_dummy_040 x y)), ((nb079_alpha_dummy_035 A), (nb079_alpha_dummy_036 x y)), ((nb079_alpha_dummy_031 A), (nb079_alpha_dummy_033 x y)), ((nb079_alpha_dummy_032 A), (nb079_alpha_dummy_034 x y)), ((nb079_alpha_dummy_057 A), (nb079_alpha_dummy_058 x y)), ((nb079_alpha_dummy_055 A), (nb079_alpha_dummy_056 x y)), ((nb079_alpha_dummy_024 A), (nb079_alpha_dummy_026 x y)), ((nb079_alpha_dummy_023 A), (nb079_alpha_dummy_025 x y)), ((nb079_alpha_dummy_053 A), (nb079_alpha_dummy_054 x y)), ((nb079_alpha_dummy_027 A), (nb079_alpha_dummy_028 x y)), ((nb079_alpha_dummy_001 A), y), ((nb079_alpha_dummy_000 A), x), ((nb079_alpha_dummy_002 A), z)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb079_compact_envfresh_0003 x y z A)

theorem nb079_wpp_notmem_0078 (A : Class) : (nb079_alpha_dummy_057 A) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_057, fv_syn_c0] using (nb079_compact_fv_empty_0026 A)

theorem nb079_wpp_notmem_0079 (x : Var) (y : Var) : (nb079_alpha_dummy_058 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_058, fv_syn_c0] using (nb079_compact_fv_empty_0027 x y)

theorem nb079_wpp_notmem_0080 (A : Class) : (nb079_alpha_dummy_055 A) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_055, fv_syn_c0] using (nb079_compact_fv_empty_0028 A)

theorem nb079_wpp_notmem_0081 (x : Var) (y : Var) : (nb079_alpha_dummy_056 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_056, fv_syn_c0] using (nb079_compact_fv_empty_0029 x y)

theorem nb079_wpp_notmem_0082 (A : Class) : (nb079_alpha_dummy_053 A) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_053, fv_syn_c0] using (nb079_compact_fv_empty_0030 A)

theorem nb079_wpp_notmem_0083 (x : Var) (y : Var) : (nb079_alpha_dummy_054 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_054, fv_syn_c0] using (nb079_compact_fv_empty_0031 x y)

theorem nb079_compact_envfresh_0004 (x : Var) (y : Var) (z : Var) (A : Class) : TEnvFresh [((nb079_alpha_dummy_039 A), (nb079_alpha_dummy_042 x y)), ((nb079_alpha_dummy_038 A), (nb079_alpha_dummy_041 x y)), ((nb079_alpha_dummy_037 A), (nb079_alpha_dummy_040 x y)), ((nb079_alpha_dummy_035 A), (nb079_alpha_dummy_036 x y)), ((nb079_alpha_dummy_031 A), (nb079_alpha_dummy_033 x y)), ((nb079_alpha_dummy_032 A), (nb079_alpha_dummy_034 x y)), ((nb079_alpha_dummy_057 A), (nb079_alpha_dummy_058 x y)), ((nb079_alpha_dummy_055 A), (nb079_alpha_dummy_056 x y)), ((nb079_alpha_dummy_024 A), (nb079_alpha_dummy_026 x y)), ((nb079_alpha_dummy_023 A), (nb079_alpha_dummy_025 x y)), ((nb079_alpha_dummy_053 A), (nb079_alpha_dummy_054 x y)), ((nb079_alpha_dummy_027 A), (nb079_alpha_dummy_028 x y)), ((nb079_alpha_dummy_001 A), y), ((nb079_alpha_dummy_000 A), x), ((nb079_alpha_dummy_002 A), z)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb079_alpha_dummy_039 A) (nb079_alpha_dummy_042 x y) (nb079_wpp_notmem_0026 A) (nb079_wpp_notmem_0027 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_038 A) (nb079_alpha_dummy_041 x y) (nb079_wpp_notmem_0028 A) (nb079_wpp_notmem_0029 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_037 A) (nb079_alpha_dummy_040 x y) (nb079_wpp_notmem_0030 A) (nb079_wpp_notmem_0031 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_035 A) (nb079_alpha_dummy_036 x y) (nb079_wpp_notmem_0032 A) (nb079_wpp_notmem_0033 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_031 A) (nb079_alpha_dummy_033 x y) (nb079_wpp_notmem_0034 A) (nb079_wpp_notmem_0035 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_032 A) (nb079_alpha_dummy_034 x y) (nb079_wpp_notmem_0036 A) (nb079_wpp_notmem_0037 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_057 A) (nb079_alpha_dummy_058 x y) (nb079_wpp_notmem_0078 A) (nb079_wpp_notmem_0079 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_055 A) (nb079_alpha_dummy_056 x y) (nb079_wpp_notmem_0080 A) (nb079_wpp_notmem_0081 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_024 A) (nb079_alpha_dummy_026 x y) (nb079_wpp_notmem_0038 A) (nb079_wpp_notmem_0039 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_023 A) (nb079_alpha_dummy_025 x y) (nb079_wpp_notmem_0040 A) (nb079_wpp_notmem_0041 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_053 A) (nb079_alpha_dummy_054 x y) (nb079_wpp_notmem_0082 A) (nb079_wpp_notmem_0083 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_027 A) (nb079_alpha_dummy_028 x y) (nb079_wpp_notmem_0044 A) (nb079_wpp_notmem_0045 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_001 A) y (nb079_wpp_notmem_0046 A) (nb079_wpp_notmem_0047 y) (TEnvFresh.consFresh (nb079_alpha_dummy_000 A) x (nb079_wpp_notmem_0048 A) (nb079_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb079_alpha_dummy_002 A) z (nb079_wpp_notmem_0050 A) (nb079_wpp_notmem_0051 z) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))

noncomputable def nb079_wpp_refl_0004 (x : Var) (y : Var) (z : Var) (A : Class) : TReflOn [((nb079_alpha_dummy_039 A), (nb079_alpha_dummy_042 x y)), ((nb079_alpha_dummy_038 A), (nb079_alpha_dummy_041 x y)), ((nb079_alpha_dummy_037 A), (nb079_alpha_dummy_040 x y)), ((nb079_alpha_dummy_035 A), (nb079_alpha_dummy_036 x y)), ((nb079_alpha_dummy_031 A), (nb079_alpha_dummy_033 x y)), ((nb079_alpha_dummy_032 A), (nb079_alpha_dummy_034 x y)), ((nb079_alpha_dummy_057 A), (nb079_alpha_dummy_058 x y)), ((nb079_alpha_dummy_055 A), (nb079_alpha_dummy_056 x y)), ((nb079_alpha_dummy_024 A), (nb079_alpha_dummy_026 x y)), ((nb079_alpha_dummy_023 A), (nb079_alpha_dummy_025 x y)), ((nb079_alpha_dummy_053 A), (nb079_alpha_dummy_054 x y)), ((nb079_alpha_dummy_027 A), (nb079_alpha_dummy_028 x y)), ((nb079_alpha_dummy_001 A), y), ((nb079_alpha_dummy_000 A), x), ((nb079_alpha_dummy_002 A), z)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb079_compact_envfresh_0004 x y z A)

theorem nb079_wpp_notmem_0084 (A : Class) : (nb079_alpha_dummy_057 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb079_alpha_dummy_057, fv_syn_cnnc] using (nb079_compact_fv_empty_0026 A)

theorem nb079_wpp_notmem_0085 (x : Var) (y : Var) : (nb079_alpha_dummy_058 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb079_alpha_dummy_058, fv_syn_cnnc] using (nb079_compact_fv_empty_0027 x y)

theorem nb079_wpp_notmem_0086 (A : Class) : (nb079_alpha_dummy_055 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb079_alpha_dummy_055, fv_syn_cnnc] using (nb079_compact_fv_empty_0028 A)

theorem nb079_wpp_notmem_0087 (x : Var) (y : Var) : (nb079_alpha_dummy_056 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb079_alpha_dummy_056, fv_syn_cnnc] using (nb079_compact_fv_empty_0029 x y)

theorem nb079_wpp_notmem_0088 (A : Class) : (nb079_alpha_dummy_053 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb079_alpha_dummy_053, fv_syn_cnnc] using (nb079_compact_fv_empty_0030 A)

theorem nb079_wpp_notmem_0089 (x : Var) (y : Var) : (nb079_alpha_dummy_054 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb079_alpha_dummy_054, fv_syn_cnnc] using (nb079_compact_fv_empty_0031 x y)

theorem nb079_compact_envfresh_0005 (x : Var) (y : Var) (z : Var) (A : Class) : TEnvFresh [((nb079_alpha_dummy_035 A), (nb079_alpha_dummy_036 x y)), ((nb079_alpha_dummy_031 A), (nb079_alpha_dummy_033 x y)), ((nb079_alpha_dummy_032 A), (nb079_alpha_dummy_034 x y)), ((nb079_alpha_dummy_057 A), (nb079_alpha_dummy_058 x y)), ((nb079_alpha_dummy_055 A), (nb079_alpha_dummy_056 x y)), ((nb079_alpha_dummy_024 A), (nb079_alpha_dummy_026 x y)), ((nb079_alpha_dummy_023 A), (nb079_alpha_dummy_025 x y)), ((nb079_alpha_dummy_053 A), (nb079_alpha_dummy_054 x y)), ((nb079_alpha_dummy_027 A), (nb079_alpha_dummy_028 x y)), ((nb079_alpha_dummy_001 A), y), ((nb079_alpha_dummy_000 A), x), ((nb079_alpha_dummy_002 A), z)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb079_alpha_dummy_035 A) (nb079_alpha_dummy_036 x y) (nb079_wpp_notmem_0052 A) (nb079_wpp_notmem_0053 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_031 A) (nb079_alpha_dummy_033 x y) (nb079_wpp_notmem_0054 A) (nb079_wpp_notmem_0055 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_032 A) (nb079_alpha_dummy_034 x y) (nb079_wpp_notmem_0056 A) (nb079_wpp_notmem_0057 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_057 A) (nb079_alpha_dummy_058 x y) (nb079_wpp_notmem_0084 A) (nb079_wpp_notmem_0085 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_055 A) (nb079_alpha_dummy_056 x y) (nb079_wpp_notmem_0086 A) (nb079_wpp_notmem_0087 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_024 A) (nb079_alpha_dummy_026 x y) (nb079_wpp_notmem_0058 A) (nb079_wpp_notmem_0059 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_023 A) (nb079_alpha_dummy_025 x y) (nb079_wpp_notmem_0060 A) (nb079_wpp_notmem_0061 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_053 A) (nb079_alpha_dummy_054 x y) (nb079_wpp_notmem_0088 A) (nb079_wpp_notmem_0089 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_027 A) (nb079_alpha_dummy_028 x y) (nb079_wpp_notmem_0064 A) (nb079_wpp_notmem_0065 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_001 A) y (nb079_wpp_notmem_0066 A) (nb079_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb079_alpha_dummy_000 A) x (nb079_wpp_notmem_0068 A) (nb079_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb079_alpha_dummy_002 A) z (nb079_wpp_notmem_0070 A) (nb079_wpp_notmem_0071 z) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))

noncomputable def nb079_wpp_refl_0005 (x : Var) (y : Var) (z : Var) (A : Class) : TReflOn [((nb079_alpha_dummy_035 A), (nb079_alpha_dummy_036 x y)), ((nb079_alpha_dummy_031 A), (nb079_alpha_dummy_033 x y)), ((nb079_alpha_dummy_032 A), (nb079_alpha_dummy_034 x y)), ((nb079_alpha_dummy_057 A), (nb079_alpha_dummy_058 x y)), ((nb079_alpha_dummy_055 A), (nb079_alpha_dummy_056 x y)), ((nb079_alpha_dummy_024 A), (nb079_alpha_dummy_026 x y)), ((nb079_alpha_dummy_023 A), (nb079_alpha_dummy_025 x y)), ((nb079_alpha_dummy_053 A), (nb079_alpha_dummy_054 x y)), ((nb079_alpha_dummy_027 A), (nb079_alpha_dummy_028 x y)), ((nb079_alpha_dummy_001 A), y), ((nb079_alpha_dummy_000 A), x), ((nb079_alpha_dummy_002 A), z)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb079_compact_envfresh_0005 x y z A)

theorem nb079_wpp_notmem_0090 (A : Class) : (nb079_alpha_dummy_055 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb079_alpha_dummy_055, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb079_compact_fv_empty_0028 A)

theorem nb079_wpp_notmem_0091 (x : Var) (y : Var) : (nb079_alpha_dummy_056 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb079_alpha_dummy_056, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb079_compact_fv_empty_0029 x y)

theorem nb079_wpp_notmem_0092 (A : Class) : (nb079_alpha_dummy_024 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb079_alpha_dummy_024, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb079_compact_fv_empty_0012 A)

theorem nb079_wpp_notmem_0093 (x : Var) (y : Var) : (nb079_alpha_dummy_026 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb079_alpha_dummy_026, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb079_compact_fv_empty_0013 x y)

theorem nb079_wpp_notmem_0094 (A : Class) : (nb079_alpha_dummy_023 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb079_alpha_dummy_023, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb079_compact_fv_empty_0014 A)

theorem nb079_wpp_notmem_0095 (x : Var) (y : Var) : (nb079_alpha_dummy_025 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb079_alpha_dummy_025, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb079_compact_fv_empty_0015 x y)

theorem nb079_wpp_notmem_0096 (A : Class) : (nb079_alpha_dummy_053 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb079_alpha_dummy_053, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb079_compact_fv_empty_0030 A)

theorem nb079_wpp_notmem_0097 (x : Var) (y : Var) : (nb079_alpha_dummy_054 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb079_alpha_dummy_054, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb079_compact_fv_empty_0031 x y)

theorem nb079_wpp_notmem_0098 (A : Class) : (nb079_alpha_dummy_027 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb079_alpha_dummy_027, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb079_compact_fv_empty_0018 A)

theorem nb079_wpp_notmem_0099 (x : Var) (y : Var) : (nb079_alpha_dummy_028 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb079_alpha_dummy_028, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb079_compact_fv_empty_0019 x y)

theorem nb079_wpp_notmem_0100 (A : Class) : (nb079_alpha_dummy_001 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb079_alpha_dummy_001, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb079_compact_fv_empty_0020 A)

theorem nb079_wpp_notmem_0101 (y : Var) : y ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb079_compact_fv_empty_0021 y)

theorem nb079_wpp_notmem_0102 (A : Class) : (nb079_alpha_dummy_000 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb079_alpha_dummy_000, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb079_compact_fv_empty_0022 A)

theorem nb079_wpp_notmem_0103 (x : Var) : x ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb079_compact_fv_empty_0023 x)

theorem nb079_wpp_notmem_0104 (A : Class) : (nb079_alpha_dummy_002 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb079_alpha_dummy_002, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb079_compact_fv_empty_0024 A)

theorem nb079_wpp_notmem_0105 (z : Var) : z ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb079_compact_fv_empty_0025 z)

theorem nb079_compact_envfresh_0006 (x : Var) (y : Var) (z : Var) (A : Class) : TEnvFresh [((nb079_alpha_dummy_055 A), (nb079_alpha_dummy_056 x y)), ((nb079_alpha_dummy_024 A), (nb079_alpha_dummy_026 x y)), ((nb079_alpha_dummy_023 A), (nb079_alpha_dummy_025 x y)), ((nb079_alpha_dummy_053 A), (nb079_alpha_dummy_054 x y)), ((nb079_alpha_dummy_027 A), (nb079_alpha_dummy_028 x y)), ((nb079_alpha_dummy_001 A), y), ((nb079_alpha_dummy_000 A), x), ((nb079_alpha_dummy_002 A), z)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb079_alpha_dummy_055 A) (nb079_alpha_dummy_056 x y) (nb079_wpp_notmem_0090 A) (nb079_wpp_notmem_0091 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_024 A) (nb079_alpha_dummy_026 x y) (nb079_wpp_notmem_0092 A) (nb079_wpp_notmem_0093 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_023 A) (nb079_alpha_dummy_025 x y) (nb079_wpp_notmem_0094 A) (nb079_wpp_notmem_0095 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_053 A) (nb079_alpha_dummy_054 x y) (nb079_wpp_notmem_0096 A) (nb079_wpp_notmem_0097 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_027 A) (nb079_alpha_dummy_028 x y) (nb079_wpp_notmem_0098 A) (nb079_wpp_notmem_0099 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_001 A) y (nb079_wpp_notmem_0100 A) (nb079_wpp_notmem_0101 y) (TEnvFresh.consFresh (nb079_alpha_dummy_000 A) x (nb079_wpp_notmem_0102 A) (nb079_wpp_notmem_0103 x) (TEnvFresh.consFresh (nb079_alpha_dummy_002 A) z (nb079_wpp_notmem_0104 A) (nb079_wpp_notmem_0105 z) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))

noncomputable def nb079_wpp_refl_0006 (x : Var) (y : Var) (z : Var) (A : Class) : TReflOn [((nb079_alpha_dummy_055 A), (nb079_alpha_dummy_056 x y)), ((nb079_alpha_dummy_024 A), (nb079_alpha_dummy_026 x y)), ((nb079_alpha_dummy_023 A), (nb079_alpha_dummy_025 x y)), ((nb079_alpha_dummy_053 A), (nb079_alpha_dummy_054 x y)), ((nb079_alpha_dummy_027 A), (nb079_alpha_dummy_028 x y)), ((nb079_alpha_dummy_001 A), y), ((nb079_alpha_dummy_000 A), x), ((nb079_alpha_dummy_002 A), z)] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb079_compact_envfresh_0006 x y z A)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
