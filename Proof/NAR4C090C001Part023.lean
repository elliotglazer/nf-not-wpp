import NAR4C090C001Part022

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

theorem nb090_wpp_notmem_0073 (v : Var) (u : Var) : (nb090_alpha_dummy_040 v u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_040, fv_syn_c1c] using (nb090_compact_fv_empty_0027 v u)

theorem nb090_compact_fv_empty_0028 (A : Class) : (nb090_alpha_dummy_037 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0074 (A : Class) : (nb090_alpha_dummy_037 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_037, fv_syn_c1c] using (nb090_compact_fv_empty_0028 A)

theorem nb090_compact_fv_empty_0029 (v : Var) (u : Var) : (nb090_alpha_dummy_038 v u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0075 (v : Var) (u : Var) : (nb090_alpha_dummy_038 v u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_038, fv_syn_c1c] using (nb090_compact_fv_empty_0029 v u)

theorem nb090_compact_fv_empty_0030 (A : Class) : (nb090_alpha_dummy_035 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0076 (A : Class) : (nb090_alpha_dummy_035 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_035, fv_syn_c1c] using (nb090_compact_fv_empty_0030 A)

theorem nb090_compact_fv_empty_0031 (v : Var) (u : Var) : (nb090_alpha_dummy_036 v u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0077 (v : Var) (u : Var) : (nb090_alpha_dummy_036 v u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_036, fv_syn_c1c] using (nb090_compact_fv_empty_0031 v u)

theorem nb090_compact_envfresh_0003 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_021 A), (nb090_alpha_dummy_024 v u)), ((nb090_alpha_dummy_020 A), (nb090_alpha_dummy_023 v u)), ((nb090_alpha_dummy_019 A), (nb090_alpha_dummy_022 v u)), ((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A), (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)), ((nb090_alpha_dummy_039 A), (nb090_alpha_dummy_040 v u)), ((nb090_alpha_dummy_037 A), (nb090_alpha_dummy_038 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)), ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_035 A), (nb090_alpha_dummy_036 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_021 A) (nb090_alpha_dummy_024 v u) (nb090_wpp_notmem_0000 A) (nb090_wpp_notmem_0001 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_020 A) (nb090_alpha_dummy_023 v u) (nb090_wpp_notmem_0002 A) (nb090_wpp_notmem_0003 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_019 A) (nb090_alpha_dummy_022 v u) (nb090_wpp_notmem_0004 A) (nb090_wpp_notmem_0005 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_017 A) (nb090_alpha_dummy_018 v u) (nb090_wpp_notmem_0006 A) (nb090_wpp_notmem_0007 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_013 A) (nb090_alpha_dummy_015 v u) (nb090_wpp_notmem_0008 A) (nb090_wpp_notmem_0009 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_014 A) (nb090_alpha_dummy_016 v u) (nb090_wpp_notmem_0010 A) (nb090_wpp_notmem_0011 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_039 A) (nb090_alpha_dummy_040 v u) (nb090_wpp_notmem_0072 A) (nb090_wpp_notmem_0073 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_037 A) (nb090_alpha_dummy_038 v u) (nb090_wpp_notmem_0074 A) (nb090_wpp_notmem_0075 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_006 A) (nb090_alpha_dummy_008 v u) (nb090_wpp_notmem_0012 A) (nb090_wpp_notmem_0013 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_005 A) (nb090_alpha_dummy_007 v u) (nb090_wpp_notmem_0014 A) (nb090_wpp_notmem_0015 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_035 A) (nb090_alpha_dummy_036 v u) (nb090_wpp_notmem_0076 A) (nb090_wpp_notmem_0077 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_009 A) (nb090_alpha_dummy_010 v u) (nb090_wpp_notmem_0018 A) (nb090_wpp_notmem_0019 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0020 A) (nb090_wpp_notmem_0021 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0022 A) (nb090_wpp_notmem_0023 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0024 A) (nb090_wpp_notmem_0025 v u A h) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb090_wpp_refl_0003 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_021 A), (nb090_alpha_dummy_024 v u)), ((nb090_alpha_dummy_020 A), (nb090_alpha_dummy_023 v u)), ((nb090_alpha_dummy_019 A), (nb090_alpha_dummy_022 v u)), ((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A), (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)), ((nb090_alpha_dummy_039 A), (nb090_alpha_dummy_040 v u)), ((nb090_alpha_dummy_037 A), (nb090_alpha_dummy_038 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)), ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_035 A), (nb090_alpha_dummy_036 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0003 v u A h)

theorem nb090_wpp_notmem_0078 (A : Class) : (nb090_alpha_dummy_039 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_039, fv_syn_c0] using (nb090_compact_fv_empty_0026 A)

theorem nb090_wpp_notmem_0079 (v : Var) (u : Var) : (nb090_alpha_dummy_040 v u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_040, fv_syn_c0] using (nb090_compact_fv_empty_0027 v u)

theorem nb090_wpp_notmem_0080 (A : Class) : (nb090_alpha_dummy_037 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_037, fv_syn_c0] using (nb090_compact_fv_empty_0028 A)

theorem nb090_wpp_notmem_0081 (v : Var) (u : Var) : (nb090_alpha_dummy_038 v u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_038, fv_syn_c0] using (nb090_compact_fv_empty_0029 v u)

theorem nb090_wpp_notmem_0082 (A : Class) : (nb090_alpha_dummy_035 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_035, fv_syn_c0] using (nb090_compact_fv_empty_0030 A)

theorem nb090_wpp_notmem_0083 (v : Var) (u : Var) : (nb090_alpha_dummy_036 v u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_036, fv_syn_c0] using (nb090_compact_fv_empty_0031 v u)

theorem nb090_compact_envfresh_0004 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_021 A), (nb090_alpha_dummy_024 v u)), ((nb090_alpha_dummy_020 A), (nb090_alpha_dummy_023 v u)), ((nb090_alpha_dummy_019 A), (nb090_alpha_dummy_022 v u)), ((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A), (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)), ((nb090_alpha_dummy_039 A), (nb090_alpha_dummy_040 v u)), ((nb090_alpha_dummy_037 A), (nb090_alpha_dummy_038 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)), ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_035 A), (nb090_alpha_dummy_036 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_021 A) (nb090_alpha_dummy_024 v u) (nb090_wpp_notmem_0026 A) (nb090_wpp_notmem_0027 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_020 A) (nb090_alpha_dummy_023 v u) (nb090_wpp_notmem_0028 A) (nb090_wpp_notmem_0029 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_019 A) (nb090_alpha_dummy_022 v u) (nb090_wpp_notmem_0030 A) (nb090_wpp_notmem_0031 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_017 A) (nb090_alpha_dummy_018 v u) (nb090_wpp_notmem_0032 A) (nb090_wpp_notmem_0033 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_013 A) (nb090_alpha_dummy_015 v u) (nb090_wpp_notmem_0034 A) (nb090_wpp_notmem_0035 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_014 A) (nb090_alpha_dummy_016 v u) (nb090_wpp_notmem_0036 A) (nb090_wpp_notmem_0037 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_039 A) (nb090_alpha_dummy_040 v u) (nb090_wpp_notmem_0078 A) (nb090_wpp_notmem_0079 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_037 A) (nb090_alpha_dummy_038 v u) (nb090_wpp_notmem_0080 A) (nb090_wpp_notmem_0081 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_006 A) (nb090_alpha_dummy_008 v u) (nb090_wpp_notmem_0038 A) (nb090_wpp_notmem_0039 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_005 A) (nb090_alpha_dummy_007 v u) (nb090_wpp_notmem_0040 A) (nb090_wpp_notmem_0041 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_035 A) (nb090_alpha_dummy_036 v u) (nb090_wpp_notmem_0082 A) (nb090_wpp_notmem_0083 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_009 A) (nb090_alpha_dummy_010 v u) (nb090_wpp_notmem_0044 A) (nb090_wpp_notmem_0045 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0046 A) (nb090_wpp_notmem_0047 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0048 A) (nb090_wpp_notmem_0049 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0050 A) (nb090_wpp_notmem_0051 v u A h) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))

noncomputable def nb090_wpp_refl_0004 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_021 A), (nb090_alpha_dummy_024 v u)), ((nb090_alpha_dummy_020 A), (nb090_alpha_dummy_023 v u)), ((nb090_alpha_dummy_019 A), (nb090_alpha_dummy_022 v u)), ((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A), (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)), ((nb090_alpha_dummy_039 A), (nb090_alpha_dummy_040 v u)), ((nb090_alpha_dummy_037 A), (nb090_alpha_dummy_038 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)), ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_035 A), (nb090_alpha_dummy_036 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0004 v u A h)

theorem nb090_wpp_notmem_0084 (A : Class) : (nb090_alpha_dummy_039 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_039, fv_syn_cnnc] using (nb090_compact_fv_empty_0026 A)

theorem nb090_wpp_notmem_0085 (v : Var) (u : Var) : (nb090_alpha_dummy_040 v u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_040, fv_syn_cnnc] using (nb090_compact_fv_empty_0027 v u)

theorem nb090_wpp_notmem_0086 (A : Class) : (nb090_alpha_dummy_037 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_037, fv_syn_cnnc] using (nb090_compact_fv_empty_0028 A)

theorem nb090_wpp_notmem_0087 (v : Var) (u : Var) : (nb090_alpha_dummy_038 v u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_038, fv_syn_cnnc] using (nb090_compact_fv_empty_0029 v u)

theorem nb090_wpp_notmem_0088 (A : Class) : (nb090_alpha_dummy_035 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_035, fv_syn_cnnc] using (nb090_compact_fv_empty_0030 A)

theorem nb090_wpp_notmem_0089 (v : Var) (u : Var) : (nb090_alpha_dummy_036 v u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_036, fv_syn_cnnc] using (nb090_compact_fv_empty_0031 v u)

theorem nb090_compact_envfresh_0005 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A), (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)), ((nb090_alpha_dummy_039 A), (nb090_alpha_dummy_040 v u)), ((nb090_alpha_dummy_037 A), (nb090_alpha_dummy_038 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)), ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_035 A), (nb090_alpha_dummy_036 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_017 A) (nb090_alpha_dummy_018 v u) (nb090_wpp_notmem_0052 A) (nb090_wpp_notmem_0053 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_013 A) (nb090_alpha_dummy_015 v u) (nb090_wpp_notmem_0054 A) (nb090_wpp_notmem_0055 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_014 A) (nb090_alpha_dummy_016 v u) (nb090_wpp_notmem_0056 A) (nb090_wpp_notmem_0057 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_039 A) (nb090_alpha_dummy_040 v u) (nb090_wpp_notmem_0084 A) (nb090_wpp_notmem_0085 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_037 A) (nb090_alpha_dummy_038 v u) (nb090_wpp_notmem_0086 A) (nb090_wpp_notmem_0087 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_006 A) (nb090_alpha_dummy_008 v u) (nb090_wpp_notmem_0058 A) (nb090_wpp_notmem_0059 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_005 A) (nb090_alpha_dummy_007 v u) (nb090_wpp_notmem_0060 A) (nb090_wpp_notmem_0061 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_035 A) (nb090_alpha_dummy_036 v u) (nb090_wpp_notmem_0088 A) (nb090_wpp_notmem_0089 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_009 A) (nb090_alpha_dummy_010 v u) (nb090_wpp_notmem_0064 A) (nb090_wpp_notmem_0065 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0066 A) (nb090_wpp_notmem_0067 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0068 A) (nb090_wpp_notmem_0069 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0070 A) (nb090_wpp_notmem_0071 v u A h) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))

noncomputable def nb090_wpp_refl_0005 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A), (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)), ((nb090_alpha_dummy_039 A), (nb090_alpha_dummy_040 v u)), ((nb090_alpha_dummy_037 A), (nb090_alpha_dummy_038 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)), ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_035 A), (nb090_alpha_dummy_036 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0005 v u A h)

theorem nb090_wpp_notmem_0090 (A : Class) : (nb090_alpha_dummy_037 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_037, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0028 A)

theorem nb090_wpp_notmem_0091 (v : Var) (u : Var) : (nb090_alpha_dummy_038 v u) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_038, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0029 v u)

theorem nb090_wpp_notmem_0092 (A : Class) : (nb090_alpha_dummy_006 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_006, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0012 A)

theorem nb090_wpp_notmem_0093 (v : Var) (u : Var) : (nb090_alpha_dummy_008 v u) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_008, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0013 v u)

theorem nb090_wpp_notmem_0094 (A : Class) : (nb090_alpha_dummy_005 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_005, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0014 A)

theorem nb090_wpp_notmem_0095 (v : Var) (u : Var) : (nb090_alpha_dummy_007 v u) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_007, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0015 v u)

theorem nb090_wpp_notmem_0096 (A : Class) : (nb090_alpha_dummy_035 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_035, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0030 A)

theorem nb090_wpp_notmem_0097 (v : Var) (u : Var) : (nb090_alpha_dummy_036 v u) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_036, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0031 v u)

theorem nb090_wpp_notmem_0098 (A : Class) : (nb090_alpha_dummy_009 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_009, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0018 A)

theorem nb090_wpp_notmem_0099 (v : Var) (u : Var) : (nb090_alpha_dummy_010 v u) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_010, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0019 v u)

theorem nb090_wpp_notmem_0100 (A : Class) : (nb090_alpha_dummy_002 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_002, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0020 A)

theorem nb090_wpp_notmem_0101 (v : Var) : v ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0021 v)

theorem nb090_wpp_notmem_0102 (A : Class) : (nb090_alpha_dummy_001 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_001, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0022 A)

theorem nb090_wpp_notmem_0103 (u : Var) : u ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0023 u)

theorem nb090_wpp_notmem_0104 (A : Class) : (nb090_alpha_dummy_003 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_003, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0024 A)

theorem nb090_wpp_notmem_0105 (v : Var) (u : Var) (A : Class) (h : Var) : (nb090_alpha_dummy_004 v u A h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_004, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0025 v u A h)

theorem nb090_compact_envfresh_0006 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_037 A), (nb090_alpha_dummy_038 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)), ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_035 A), (nb090_alpha_dummy_036 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_037 A) (nb090_alpha_dummy_038 v u) (nb090_wpp_notmem_0090 A) (nb090_wpp_notmem_0091 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_006 A) (nb090_alpha_dummy_008 v u) (nb090_wpp_notmem_0092 A) (nb090_wpp_notmem_0093 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_005 A) (nb090_alpha_dummy_007 v u) (nb090_wpp_notmem_0094 A) (nb090_wpp_notmem_0095 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_035 A) (nb090_alpha_dummy_036 v u) (nb090_wpp_notmem_0096 A) (nb090_wpp_notmem_0097 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_009 A) (nb090_alpha_dummy_010 v u) (nb090_wpp_notmem_0098 A) (nb090_wpp_notmem_0099 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0100 A) (nb090_wpp_notmem_0101 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0102 A) (nb090_wpp_notmem_0103 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0104 A) (nb090_wpp_notmem_0105 v u A h) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))

noncomputable def nb090_wpp_refl_0006 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_037 A), (nb090_alpha_dummy_038 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)), ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_035 A), (nb090_alpha_dummy_036 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0006 v u A h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
