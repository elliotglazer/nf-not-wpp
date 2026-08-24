import NAR4H5C093M3Part002

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

theorem nb093_compact_fv_empty_0057 (r : Var) : (nb093_alpha_dummy_061 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0147 (r : Var) : (nb093_alpha_dummy_061 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_061, fv_syn_c1c] using (nb093_compact_fv_empty_0057 r)

theorem nb093_compact_fv_empty_0058 (A : Class) : (nb093_alpha_dummy_058 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0148 (A : Class) : (nb093_alpha_dummy_058 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_058, fv_syn_c1c] using (nb093_compact_fv_empty_0058 A)

theorem nb093_compact_fv_empty_0059 (r : Var) : (nb093_alpha_dummy_060 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0149 (r : Var) : (nb093_alpha_dummy_060 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_060, fv_syn_c1c] using (nb093_compact_fv_empty_0059 r)

theorem nb093_compact_fv_empty_0060 (A : Class) : (nb093_alpha_dummy_062 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0150 (A : Class) : (nb093_alpha_dummy_062 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_062, fv_syn_c1c] using (nb093_compact_fv_empty_0060 A)

theorem nb093_compact_fv_empty_0061 (r : Var) : (nb093_alpha_dummy_063 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0151 (r : Var) : (nb093_alpha_dummy_063 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_063, fv_syn_c1c] using (nb093_compact_fv_empty_0061 r)

theorem nb093_compact_fv_empty_0062 (A : Class) : (nb093_alpha_dummy_056 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0152 (A : Class) : (nb093_alpha_dummy_056 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_056, fv_syn_c1c] using (nb093_compact_fv_empty_0062 A)

theorem nb093_compact_fv_empty_0063 (r : Var) : (nb093_alpha_dummy_057 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0153 (r : Var) : (nb093_alpha_dummy_057 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_057, fv_syn_c1c] using (nb093_compact_fv_empty_0063 r)

theorem nb093_compact_fv_empty_0064 (A : Class) : (nb093_alpha_dummy_054 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0154 (A : Class) : (nb093_alpha_dummy_054 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_054, fv_syn_c1c] using (nb093_compact_fv_empty_0064 A)

theorem nb093_compact_fv_empty_0065 (r : Var) : (nb093_alpha_dummy_055 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0155 (r : Var) : (nb093_alpha_dummy_055 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_055, fv_syn_c1c] using (nb093_compact_fv_empty_0065 r)

theorem nb093_compact_fv_empty_0066 (A : Class) : (nb093_alpha_dummy_052 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0156 (A : Class) : (nb093_alpha_dummy_052 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_052, fv_syn_c1c] using (nb093_compact_fv_empty_0066 A)

theorem nb093_compact_fv_empty_0067 (r : Var) : (nb093_alpha_dummy_053 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0157 (r : Var) : (nb093_alpha_dummy_053 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_053, fv_syn_c1c] using (nb093_compact_fv_empty_0067 r)

theorem nb093_compact_fv_empty_0068 (A : Class) : (nb093_alpha_dummy_045 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0158 (A : Class) : (nb093_alpha_dummy_045 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_045, fv_syn_c1c] using (nb093_compact_fv_empty_0068 A)

theorem nb093_compact_fv_empty_0069 (r : Var) (d : Var) : (nb093_alpha_dummy_047 r d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0159 (r : Var) (d : Var) : (nb093_alpha_dummy_047 r d) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_047, fv_syn_c1c] using (nb093_compact_fv_empty_0069 r d)

theorem nb093_compact_fv_empty_0070 (A : Class) : (nb093_alpha_dummy_044 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0160 (A : Class) : (nb093_alpha_dummy_044 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_044, fv_syn_c1c] using (nb093_compact_fv_empty_0070 A)

theorem nb093_compact_fv_empty_0071 (r : Var) (d : Var) : (nb093_alpha_dummy_046 r d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0161 (r : Var) (d : Var) : (nb093_alpha_dummy_046 r d) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_046, fv_syn_c1c] using (nb093_compact_fv_empty_0071 r d)

theorem nb093_compact_fv_empty_0072 (A : Class) : (nb093_alpha_dummy_050 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0162 (A : Class) : (nb093_alpha_dummy_050 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_050, fv_syn_c1c] using (nb093_compact_fv_empty_0072 A)

theorem nb093_compact_fv_empty_0073 (r : Var) (d : Var) : (nb093_alpha_dummy_051 r d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0163 (r : Var) (d : Var) : (nb093_alpha_dummy_051 r d) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_051, fv_syn_c1c] using (nb093_compact_fv_empty_0073 r d)

theorem nb093_compact_fv_empty_0074 (A : Class) : (nb093_alpha_dummy_048 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0164 (A : Class) : (nb093_alpha_dummy_048 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_048, fv_syn_c1c] using (nb093_compact_fv_empty_0074 A)

theorem nb093_compact_fv_empty_0075 (r : Var) (d : Var) : (nb093_alpha_dummy_049 r d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0165 (r : Var) (d : Var) : (nb093_alpha_dummy_049 r d) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_049, fv_syn_c1c] using (nb093_compact_fv_empty_0075 r d)

theorem nb093_compact_envfresh_0008 (A : Class) (r : Var) (d : Var) : TEnvFresh [((nb093_alpha_dummy_080 A), (nb093_alpha_dummy_083 r)), ((nb093_alpha_dummy_079 A), (nb093_alpha_dummy_082 r)), ((nb093_alpha_dummy_078 A), (nb093_alpha_dummy_081 r)), ((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_070 A), (nb093_alpha_dummy_071 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb093_alpha_dummy_080 A) (nb093_alpha_dummy_083 r) (nb093_wpp_notmem_0126 A) (nb093_wpp_notmem_0127 r) (TEnvFresh.consFresh (nb093_alpha_dummy_079 A) (nb093_alpha_dummy_082 r) (nb093_wpp_notmem_0128 A) (nb093_wpp_notmem_0129 r) (TEnvFresh.consFresh (nb093_alpha_dummy_078 A) (nb093_alpha_dummy_081 r) (nb093_wpp_notmem_0130 A) (nb093_wpp_notmem_0131 r) (TEnvFresh.consFresh (nb093_alpha_dummy_076 A) (nb093_alpha_dummy_077 r) (nb093_wpp_notmem_0132 A) (nb093_wpp_notmem_0133 r) (TEnvFresh.consFresh (nb093_alpha_dummy_072 A) (nb093_alpha_dummy_074 r) (nb093_wpp_notmem_0134 A) (nb093_wpp_notmem_0135 r) (TEnvFresh.consFresh (nb093_alpha_dummy_073 A) (nb093_alpha_dummy_075 r) (nb093_wpp_notmem_0136 A) (nb093_wpp_notmem_0137 r) (TEnvFresh.consFresh (nb093_alpha_dummy_065 A) (nb093_alpha_dummy_067 r) (nb093_wpp_notmem_0138 A) (nb093_wpp_notmem_0139 r) (TEnvFresh.consFresh (nb093_alpha_dummy_064 A) (nb093_alpha_dummy_066 r) (nb093_wpp_notmem_0140 A) (nb093_wpp_notmem_0141 r) (TEnvFresh.consFresh (nb093_alpha_dummy_070 A) (nb093_alpha_dummy_071 r) (nb093_wpp_notmem_0142 A) (nb093_wpp_notmem_0143 r) (TEnvFresh.consFresh (nb093_alpha_dummy_068 A) (nb093_alpha_dummy_069 r) (nb093_wpp_notmem_0144 A) (nb093_wpp_notmem_0145 r) (TEnvFresh.consFresh (nb093_alpha_dummy_059 A) (nb093_alpha_dummy_061 r) (nb093_wpp_notmem_0146 A) (nb093_wpp_notmem_0147 r) (TEnvFresh.consFresh (nb093_alpha_dummy_058 A) (nb093_alpha_dummy_060 r) (nb093_wpp_notmem_0148 A) (nb093_wpp_notmem_0149 r) (TEnvFresh.consFresh (nb093_alpha_dummy_062 A) (nb093_alpha_dummy_063 r) (nb093_wpp_notmem_0150 A) (nb093_wpp_notmem_0151 r) (TEnvFresh.consFresh (nb093_alpha_dummy_056 A) (nb093_alpha_dummy_057 r) (nb093_wpp_notmem_0152 A) (nb093_wpp_notmem_0153 r) (TEnvFresh.consFresh (nb093_alpha_dummy_054 A) (nb093_alpha_dummy_055 r) (nb093_wpp_notmem_0154 A) (nb093_wpp_notmem_0155 r) (TEnvFresh.consFresh (nb093_alpha_dummy_052 A) (nb093_alpha_dummy_053 r) (nb093_wpp_notmem_0156 A) (nb093_wpp_notmem_0157 r) (TEnvFresh.consFresh (nb093_alpha_dummy_045 A) (nb093_alpha_dummy_047 r d) (nb093_wpp_notmem_0158 A) (nb093_wpp_notmem_0159 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_044 A) (nb093_alpha_dummy_046 r d) (nb093_wpp_notmem_0160 A) (nb093_wpp_notmem_0161 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_050 A) (nb093_alpha_dummy_051 r d) (nb093_wpp_notmem_0162 A) (nb093_wpp_notmem_0163 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_048 A) (nb093_alpha_dummy_049 r d) (nb093_wpp_notmem_0164 A) (nb093_wpp_notmem_0165 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_000 A) d (nb093_wpp_notmem_0024 A) (nb093_wpp_notmem_0025 d) (TEnvFresh.consFresh (nb093_alpha_dummy_001 A) r (nb093_wpp_notmem_0026 A) (nb093_wpp_notmem_0027 r) (TEnvFresh.consFresh (nb093_alpha_dummy_006 A) (nb093_alpha_dummy_007 r d) (nb093_wpp_notmem_0028 A) (nb093_wpp_notmem_0029 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_004 A) (nb093_alpha_dummy_005 A r d) (nb093_wpp_notmem_0030 A) (nb093_wpp_notmem_0031 A r d) (TEnvFresh.consFresh (nb093_alpha_dummy_002 A) (nb093_alpha_dummy_003 A r d) (nb093_wpp_notmem_0032 A) (nb093_wpp_notmem_0033 A r d) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))))))))

noncomputable def nb093_wpp_refl_0008 (A : Class) (r : Var) (d : Var) : TReflOn [((nb093_alpha_dummy_080 A), (nb093_alpha_dummy_083 r)), ((nb093_alpha_dummy_079 A), (nb093_alpha_dummy_082 r)), ((nb093_alpha_dummy_078 A), (nb093_alpha_dummy_081 r)), ((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_070 A), (nb093_alpha_dummy_071 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb093_compact_envfresh_0008 A r d)

theorem nb093_wpp_notmem_0166 (A : Class) : (nb093_alpha_dummy_080 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_080, fv_syn_c0] using (nb093_compact_fv_empty_0036 A)

theorem nb093_wpp_notmem_0167 (r : Var) : (nb093_alpha_dummy_083 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_083, fv_syn_c0] using (nb093_compact_fv_empty_0037 r)

theorem nb093_wpp_notmem_0168 (A : Class) : (nb093_alpha_dummy_079 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_079, fv_syn_c0] using (nb093_compact_fv_empty_0038 A)

theorem nb093_wpp_notmem_0169 (r : Var) : (nb093_alpha_dummy_082 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_082, fv_syn_c0] using (nb093_compact_fv_empty_0039 r)

theorem nb093_wpp_notmem_0170 (A : Class) : (nb093_alpha_dummy_078 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_078, fv_syn_c0] using (nb093_compact_fv_empty_0040 A)

theorem nb093_wpp_notmem_0171 (r : Var) : (nb093_alpha_dummy_081 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_081, fv_syn_c0] using (nb093_compact_fv_empty_0041 r)

theorem nb093_wpp_notmem_0172 (A : Class) : (nb093_alpha_dummy_076 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_076, fv_syn_c0] using (nb093_compact_fv_empty_0042 A)

theorem nb093_wpp_notmem_0173 (r : Var) : (nb093_alpha_dummy_077 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_077, fv_syn_c0] using (nb093_compact_fv_empty_0043 r)

theorem nb093_wpp_notmem_0174 (A : Class) : (nb093_alpha_dummy_072 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_072, fv_syn_c0] using (nb093_compact_fv_empty_0044 A)

theorem nb093_wpp_notmem_0175 (r : Var) : (nb093_alpha_dummy_074 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_074, fv_syn_c0] using (nb093_compact_fv_empty_0045 r)

theorem nb093_wpp_notmem_0176 (A : Class) : (nb093_alpha_dummy_073 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_073, fv_syn_c0] using (nb093_compact_fv_empty_0046 A)

theorem nb093_wpp_notmem_0177 (r : Var) : (nb093_alpha_dummy_075 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_075, fv_syn_c0] using (nb093_compact_fv_empty_0047 r)

theorem nb093_wpp_notmem_0178 (A : Class) : (nb093_alpha_dummy_065 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_065, fv_syn_c0] using (nb093_compact_fv_empty_0048 A)

theorem nb093_wpp_notmem_0179 (r : Var) : (nb093_alpha_dummy_067 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_067, fv_syn_c0] using (nb093_compact_fv_empty_0049 r)

theorem nb093_wpp_notmem_0180 (A : Class) : (nb093_alpha_dummy_064 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_064, fv_syn_c0] using (nb093_compact_fv_empty_0050 A)

theorem nb093_wpp_notmem_0181 (r : Var) : (nb093_alpha_dummy_066 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_066, fv_syn_c0] using (nb093_compact_fv_empty_0051 r)

theorem nb093_wpp_notmem_0182 (A : Class) : (nb093_alpha_dummy_070 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_070, fv_syn_c0] using (nb093_compact_fv_empty_0052 A)

theorem nb093_wpp_notmem_0183 (r : Var) : (nb093_alpha_dummy_071 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_071, fv_syn_c0] using (nb093_compact_fv_empty_0053 r)

theorem nb093_wpp_notmem_0184 (A : Class) : (nb093_alpha_dummy_068 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_068, fv_syn_c0] using (nb093_compact_fv_empty_0054 A)

theorem nb093_wpp_notmem_0185 (r : Var) : (nb093_alpha_dummy_069 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_069, fv_syn_c0] using (nb093_compact_fv_empty_0055 r)

theorem nb093_wpp_notmem_0186 (A : Class) : (nb093_alpha_dummy_059 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_059, fv_syn_c0] using (nb093_compact_fv_empty_0056 A)

theorem nb093_wpp_notmem_0187 (r : Var) : (nb093_alpha_dummy_061 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_061, fv_syn_c0] using (nb093_compact_fv_empty_0057 r)

theorem nb093_wpp_notmem_0188 (A : Class) : (nb093_alpha_dummy_058 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_058, fv_syn_c0] using (nb093_compact_fv_empty_0058 A)

theorem nb093_wpp_notmem_0189 (r : Var) : (nb093_alpha_dummy_060 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_060, fv_syn_c0] using (nb093_compact_fv_empty_0059 r)

theorem nb093_wpp_notmem_0190 (A : Class) : (nb093_alpha_dummy_062 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_062, fv_syn_c0] using (nb093_compact_fv_empty_0060 A)

theorem nb093_wpp_notmem_0191 (r : Var) : (nb093_alpha_dummy_063 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_063, fv_syn_c0] using (nb093_compact_fv_empty_0061 r)

theorem nb093_wpp_notmem_0192 (A : Class) : (nb093_alpha_dummy_056 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_056, fv_syn_c0] using (nb093_compact_fv_empty_0062 A)

theorem nb093_wpp_notmem_0193 (r : Var) : (nb093_alpha_dummy_057 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_057, fv_syn_c0] using (nb093_compact_fv_empty_0063 r)

theorem nb093_wpp_notmem_0194 (A : Class) : (nb093_alpha_dummy_054 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_054, fv_syn_c0] using (nb093_compact_fv_empty_0064 A)

theorem nb093_wpp_notmem_0195 (r : Var) : (nb093_alpha_dummy_055 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_055, fv_syn_c0] using (nb093_compact_fv_empty_0065 r)

theorem nb093_wpp_notmem_0196 (A : Class) : (nb093_alpha_dummy_052 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_052, fv_syn_c0] using (nb093_compact_fv_empty_0066 A)

theorem nb093_wpp_notmem_0197 (r : Var) : (nb093_alpha_dummy_053 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_053, fv_syn_c0] using (nb093_compact_fv_empty_0067 r)

theorem nb093_wpp_notmem_0198 (A : Class) : (nb093_alpha_dummy_045 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_045, fv_syn_c0] using (nb093_compact_fv_empty_0068 A)

theorem nb093_wpp_notmem_0199 (r : Var) (d : Var) : (nb093_alpha_dummy_047 r d) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_047, fv_syn_c0] using (nb093_compact_fv_empty_0069 r d)

theorem nb093_wpp_notmem_0200 (A : Class) : (nb093_alpha_dummy_044 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_044, fv_syn_c0] using (nb093_compact_fv_empty_0070 A)

theorem nb093_wpp_notmem_0201 (r : Var) (d : Var) : (nb093_alpha_dummy_046 r d) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_046, fv_syn_c0] using (nb093_compact_fv_empty_0071 r d)

theorem nb093_wpp_notmem_0202 (A : Class) : (nb093_alpha_dummy_050 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_050, fv_syn_c0] using (nb093_compact_fv_empty_0072 A)

theorem nb093_wpp_notmem_0203 (r : Var) (d : Var) : (nb093_alpha_dummy_051 r d) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_051, fv_syn_c0] using (nb093_compact_fv_empty_0073 r d)

theorem nb093_wpp_notmem_0204 (A : Class) : (nb093_alpha_dummy_048 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_048, fv_syn_c0] using (nb093_compact_fv_empty_0074 A)

theorem nb093_wpp_notmem_0205 (r : Var) (d : Var) : (nb093_alpha_dummy_049 r d) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_049, fv_syn_c0] using (nb093_compact_fv_empty_0075 r d)

theorem nb093_compact_envfresh_0009 (A : Class) (r : Var) (d : Var) : TEnvFresh [((nb093_alpha_dummy_080 A), (nb093_alpha_dummy_083 r)), ((nb093_alpha_dummy_079 A), (nb093_alpha_dummy_082 r)), ((nb093_alpha_dummy_078 A), (nb093_alpha_dummy_081 r)), ((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_070 A), (nb093_alpha_dummy_071 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb093_alpha_dummy_080 A) (nb093_alpha_dummy_083 r) (nb093_wpp_notmem_0166 A) (nb093_wpp_notmem_0167 r) (TEnvFresh.consFresh (nb093_alpha_dummy_079 A) (nb093_alpha_dummy_082 r) (nb093_wpp_notmem_0168 A) (nb093_wpp_notmem_0169 r) (TEnvFresh.consFresh (nb093_alpha_dummy_078 A) (nb093_alpha_dummy_081 r) (nb093_wpp_notmem_0170 A) (nb093_wpp_notmem_0171 r) (TEnvFresh.consFresh (nb093_alpha_dummy_076 A) (nb093_alpha_dummy_077 r) (nb093_wpp_notmem_0172 A) (nb093_wpp_notmem_0173 r) (TEnvFresh.consFresh (nb093_alpha_dummy_072 A) (nb093_alpha_dummy_074 r) (nb093_wpp_notmem_0174 A) (nb093_wpp_notmem_0175 r) (TEnvFresh.consFresh (nb093_alpha_dummy_073 A) (nb093_alpha_dummy_075 r) (nb093_wpp_notmem_0176 A) (nb093_wpp_notmem_0177 r) (TEnvFresh.consFresh (nb093_alpha_dummy_065 A) (nb093_alpha_dummy_067 r) (nb093_wpp_notmem_0178 A) (nb093_wpp_notmem_0179 r) (TEnvFresh.consFresh (nb093_alpha_dummy_064 A) (nb093_alpha_dummy_066 r) (nb093_wpp_notmem_0180 A) (nb093_wpp_notmem_0181 r) (TEnvFresh.consFresh (nb093_alpha_dummy_070 A) (nb093_alpha_dummy_071 r) (nb093_wpp_notmem_0182 A) (nb093_wpp_notmem_0183 r) (TEnvFresh.consFresh (nb093_alpha_dummy_068 A) (nb093_alpha_dummy_069 r) (nb093_wpp_notmem_0184 A) (nb093_wpp_notmem_0185 r) (TEnvFresh.consFresh (nb093_alpha_dummy_059 A) (nb093_alpha_dummy_061 r) (nb093_wpp_notmem_0186 A) (nb093_wpp_notmem_0187 r) (TEnvFresh.consFresh (nb093_alpha_dummy_058 A) (nb093_alpha_dummy_060 r) (nb093_wpp_notmem_0188 A) (nb093_wpp_notmem_0189 r) (TEnvFresh.consFresh (nb093_alpha_dummy_062 A) (nb093_alpha_dummy_063 r) (nb093_wpp_notmem_0190 A) (nb093_wpp_notmem_0191 r) (TEnvFresh.consFresh (nb093_alpha_dummy_056 A) (nb093_alpha_dummy_057 r) (nb093_wpp_notmem_0192 A) (nb093_wpp_notmem_0193 r) (TEnvFresh.consFresh (nb093_alpha_dummy_054 A) (nb093_alpha_dummy_055 r) (nb093_wpp_notmem_0194 A) (nb093_wpp_notmem_0195 r) (TEnvFresh.consFresh (nb093_alpha_dummy_052 A) (nb093_alpha_dummy_053 r) (nb093_wpp_notmem_0196 A) (nb093_wpp_notmem_0197 r) (TEnvFresh.consFresh (nb093_alpha_dummy_045 A) (nb093_alpha_dummy_047 r d) (nb093_wpp_notmem_0198 A) (nb093_wpp_notmem_0199 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_044 A) (nb093_alpha_dummy_046 r d) (nb093_wpp_notmem_0200 A) (nb093_wpp_notmem_0201 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_050 A) (nb093_alpha_dummy_051 r d) (nb093_wpp_notmem_0202 A) (nb093_wpp_notmem_0203 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_048 A) (nb093_alpha_dummy_049 r d) (nb093_wpp_notmem_0204 A) (nb093_wpp_notmem_0205 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_000 A) d (nb093_wpp_notmem_0054 A) (nb093_wpp_notmem_0055 d) (TEnvFresh.consFresh (nb093_alpha_dummy_001 A) r (nb093_wpp_notmem_0056 A) (nb093_wpp_notmem_0057 r) (TEnvFresh.consFresh (nb093_alpha_dummy_006 A) (nb093_alpha_dummy_007 r d) (nb093_wpp_notmem_0058 A) (nb093_wpp_notmem_0059 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_004 A) (nb093_alpha_dummy_005 A r d) (nb093_wpp_notmem_0060 A) (nb093_wpp_notmem_0061 A r d) (TEnvFresh.consFresh (nb093_alpha_dummy_002 A) (nb093_alpha_dummy_003 A r d) (nb093_wpp_notmem_0062 A) (nb093_wpp_notmem_0063 A r d) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))))))))

noncomputable def nb093_wpp_refl_0009 (A : Class) (r : Var) (d : Var) : TReflOn [((nb093_alpha_dummy_080 A), (nb093_alpha_dummy_083 r)), ((nb093_alpha_dummy_079 A), (nb093_alpha_dummy_082 r)), ((nb093_alpha_dummy_078 A), (nb093_alpha_dummy_081 r)), ((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_070 A), (nb093_alpha_dummy_071 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb093_compact_envfresh_0009 A r d)

theorem nb093_wpp_notmem_0206 (A : Class) : (nb093_alpha_dummy_076 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_076, fv_syn_cnnc] using (nb093_compact_fv_empty_0042 A)

theorem nb093_wpp_notmem_0207 (r : Var) : (nb093_alpha_dummy_077 r) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_077, fv_syn_cnnc] using (nb093_compact_fv_empty_0043 r)

theorem nb093_wpp_notmem_0208 (A : Class) : (nb093_alpha_dummy_072 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_072, fv_syn_cnnc] using (nb093_compact_fv_empty_0044 A)

theorem nb093_wpp_notmem_0209 (r : Var) : (nb093_alpha_dummy_074 r) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_074, fv_syn_cnnc] using (nb093_compact_fv_empty_0045 r)

theorem nb093_wpp_notmem_0210 (A : Class) : (nb093_alpha_dummy_073 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_073, fv_syn_cnnc] using (nb093_compact_fv_empty_0046 A)

theorem nb093_wpp_notmem_0211 (r : Var) : (nb093_alpha_dummy_075 r) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_075, fv_syn_cnnc] using (nb093_compact_fv_empty_0047 r)

theorem nb093_wpp_notmem_0212 (A : Class) : (nb093_alpha_dummy_065 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_065, fv_syn_cnnc] using (nb093_compact_fv_empty_0048 A)

theorem nb093_wpp_notmem_0213 (r : Var) : (nb093_alpha_dummy_067 r) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_067, fv_syn_cnnc] using (nb093_compact_fv_empty_0049 r)

theorem nb093_wpp_notmem_0214 (A : Class) : (nb093_alpha_dummy_064 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_064, fv_syn_cnnc] using (nb093_compact_fv_empty_0050 A)

theorem nb093_wpp_notmem_0215 (r : Var) : (nb093_alpha_dummy_066 r) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_066, fv_syn_cnnc] using (nb093_compact_fv_empty_0051 r)

theorem nb093_wpp_notmem_0216 (A : Class) : (nb093_alpha_dummy_070 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_070, fv_syn_cnnc] using (nb093_compact_fv_empty_0052 A)

theorem nb093_wpp_notmem_0217 (r : Var) : (nb093_alpha_dummy_071 r) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_071, fv_syn_cnnc] using (nb093_compact_fv_empty_0053 r)

theorem nb093_wpp_notmem_0218 (A : Class) : (nb093_alpha_dummy_068 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_068, fv_syn_cnnc] using (nb093_compact_fv_empty_0054 A)

theorem nb093_wpp_notmem_0219 (r : Var) : (nb093_alpha_dummy_069 r) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_069, fv_syn_cnnc] using (nb093_compact_fv_empty_0055 r)

theorem nb093_wpp_notmem_0220 (A : Class) : (nb093_alpha_dummy_059 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_059, fv_syn_cnnc] using (nb093_compact_fv_empty_0056 A)

theorem nb093_wpp_notmem_0221 (r : Var) : (nb093_alpha_dummy_061 r) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_061, fv_syn_cnnc] using (nb093_compact_fv_empty_0057 r)

theorem nb093_wpp_notmem_0222 (A : Class) : (nb093_alpha_dummy_058 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_058, fv_syn_cnnc] using (nb093_compact_fv_empty_0058 A)

theorem nb093_wpp_notmem_0223 (r : Var) : (nb093_alpha_dummy_060 r) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_060, fv_syn_cnnc] using (nb093_compact_fv_empty_0059 r)

theorem nb093_wpp_notmem_0224 (A : Class) : (nb093_alpha_dummy_062 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_062, fv_syn_cnnc] using (nb093_compact_fv_empty_0060 A)

theorem nb093_wpp_notmem_0225 (r : Var) : (nb093_alpha_dummy_063 r) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_063, fv_syn_cnnc] using (nb093_compact_fv_empty_0061 r)

theorem nb093_wpp_notmem_0226 (A : Class) : (nb093_alpha_dummy_056 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_056, fv_syn_cnnc] using (nb093_compact_fv_empty_0062 A)

theorem nb093_wpp_notmem_0227 (r : Var) : (nb093_alpha_dummy_057 r) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_057, fv_syn_cnnc] using (nb093_compact_fv_empty_0063 r)

theorem nb093_wpp_notmem_0228 (A : Class) : (nb093_alpha_dummy_054 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_054, fv_syn_cnnc] using (nb093_compact_fv_empty_0064 A)

theorem nb093_wpp_notmem_0229 (r : Var) : (nb093_alpha_dummy_055 r) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_055, fv_syn_cnnc] using (nb093_compact_fv_empty_0065 r)

theorem nb093_wpp_notmem_0230 (A : Class) : (nb093_alpha_dummy_052 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_052, fv_syn_cnnc] using (nb093_compact_fv_empty_0066 A)

theorem nb093_wpp_notmem_0231 (r : Var) : (nb093_alpha_dummy_053 r) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_053, fv_syn_cnnc] using (nb093_compact_fv_empty_0067 r)

theorem nb093_wpp_notmem_0232 (A : Class) : (nb093_alpha_dummy_045 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_045, fv_syn_cnnc] using (nb093_compact_fv_empty_0068 A)

theorem nb093_wpp_notmem_0233 (r : Var) (d : Var) : (nb093_alpha_dummy_047 r d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_047, fv_syn_cnnc] using (nb093_compact_fv_empty_0069 r d)

theorem nb093_wpp_notmem_0234 (A : Class) : (nb093_alpha_dummy_044 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_044, fv_syn_cnnc] using (nb093_compact_fv_empty_0070 A)

theorem nb093_wpp_notmem_0235 (r : Var) (d : Var) : (nb093_alpha_dummy_046 r d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_046, fv_syn_cnnc] using (nb093_compact_fv_empty_0071 r d)

theorem nb093_wpp_notmem_0236 (A : Class) : (nb093_alpha_dummy_050 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_050, fv_syn_cnnc] using (nb093_compact_fv_empty_0072 A)

theorem nb093_wpp_notmem_0237 (r : Var) (d : Var) : (nb093_alpha_dummy_051 r d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_051, fv_syn_cnnc] using (nb093_compact_fv_empty_0073 r d)

theorem nb093_wpp_notmem_0238 (A : Class) : (nb093_alpha_dummy_048 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_048, fv_syn_cnnc] using (nb093_compact_fv_empty_0074 A)

theorem nb093_wpp_notmem_0239 (r : Var) (d : Var) : (nb093_alpha_dummy_049 r d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_049, fv_syn_cnnc] using (nb093_compact_fv_empty_0075 r d)

theorem nb093_compact_envfresh_0010 (A : Class) (r : Var) (d : Var) : TEnvFresh [((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_070 A), (nb093_alpha_dummy_071 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb093_alpha_dummy_076 A) (nb093_alpha_dummy_077 r) (nb093_wpp_notmem_0206 A) (nb093_wpp_notmem_0207 r) (TEnvFresh.consFresh (nb093_alpha_dummy_072 A) (nb093_alpha_dummy_074 r) (nb093_wpp_notmem_0208 A) (nb093_wpp_notmem_0209 r) (TEnvFresh.consFresh (nb093_alpha_dummy_073 A) (nb093_alpha_dummy_075 r) (nb093_wpp_notmem_0210 A) (nb093_wpp_notmem_0211 r) (TEnvFresh.consFresh (nb093_alpha_dummy_065 A) (nb093_alpha_dummy_067 r) (nb093_wpp_notmem_0212 A) (nb093_wpp_notmem_0213 r) (TEnvFresh.consFresh (nb093_alpha_dummy_064 A) (nb093_alpha_dummy_066 r) (nb093_wpp_notmem_0214 A) (nb093_wpp_notmem_0215 r) (TEnvFresh.consFresh (nb093_alpha_dummy_070 A) (nb093_alpha_dummy_071 r) (nb093_wpp_notmem_0216 A) (nb093_wpp_notmem_0217 r) (TEnvFresh.consFresh (nb093_alpha_dummy_068 A) (nb093_alpha_dummy_069 r) (nb093_wpp_notmem_0218 A) (nb093_wpp_notmem_0219 r) (TEnvFresh.consFresh (nb093_alpha_dummy_059 A) (nb093_alpha_dummy_061 r) (nb093_wpp_notmem_0220 A) (nb093_wpp_notmem_0221 r) (TEnvFresh.consFresh (nb093_alpha_dummy_058 A) (nb093_alpha_dummy_060 r) (nb093_wpp_notmem_0222 A) (nb093_wpp_notmem_0223 r) (TEnvFresh.consFresh (nb093_alpha_dummy_062 A) (nb093_alpha_dummy_063 r) (nb093_wpp_notmem_0224 A) (nb093_wpp_notmem_0225 r) (TEnvFresh.consFresh (nb093_alpha_dummy_056 A) (nb093_alpha_dummy_057 r) (nb093_wpp_notmem_0226 A) (nb093_wpp_notmem_0227 r) (TEnvFresh.consFresh (nb093_alpha_dummy_054 A) (nb093_alpha_dummy_055 r) (nb093_wpp_notmem_0228 A) (nb093_wpp_notmem_0229 r) (TEnvFresh.consFresh (nb093_alpha_dummy_052 A) (nb093_alpha_dummy_053 r) (nb093_wpp_notmem_0230 A) (nb093_wpp_notmem_0231 r) (TEnvFresh.consFresh (nb093_alpha_dummy_045 A) (nb093_alpha_dummy_047 r d) (nb093_wpp_notmem_0232 A) (nb093_wpp_notmem_0233 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_044 A) (nb093_alpha_dummy_046 r d) (nb093_wpp_notmem_0234 A) (nb093_wpp_notmem_0235 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_050 A) (nb093_alpha_dummy_051 r d) (nb093_wpp_notmem_0236 A) (nb093_wpp_notmem_0237 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_048 A) (nb093_alpha_dummy_049 r d) (nb093_wpp_notmem_0238 A) (nb093_wpp_notmem_0239 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_000 A) d (nb093_wpp_notmem_0078 A) (nb093_wpp_notmem_0079 d) (TEnvFresh.consFresh (nb093_alpha_dummy_001 A) r (nb093_wpp_notmem_0080 A) (nb093_wpp_notmem_0081 r) (TEnvFresh.consFresh (nb093_alpha_dummy_006 A) (nb093_alpha_dummy_007 r d) (nb093_wpp_notmem_0082 A) (nb093_wpp_notmem_0083 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_004 A) (nb093_alpha_dummy_005 A r d) (nb093_wpp_notmem_0084 A) (nb093_wpp_notmem_0085 A r d) (TEnvFresh.consFresh (nb093_alpha_dummy_002 A) (nb093_alpha_dummy_003 A r d) (nb093_wpp_notmem_0086 A) (nb093_wpp_notmem_0087 A r d) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))))))))

noncomputable def nb093_wpp_refl_0010 (A : Class) (r : Var) (d : Var) : TReflOn [((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_070 A), (nb093_alpha_dummy_071 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb093_compact_envfresh_0010 A r d)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

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

noncomputable def nb093_split_alpha_0002 (A : Class) (r : Var) (d : Var) : TAlphaWff [((nb093_alpha_dummy_070 A), (nb093_alpha_dummy_071 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_070 A)) (Class.cab (nb093_alpha_dummy_064 A) (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_058 A)) (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A)) (syn_cphi (Class.cv (nb093_alpha_dummy_065 A))))))) (Wff.neg (Wff.classMem (Class.cv (nb093_alpha_dummy_070 A)) (Class.cab (nb093_alpha_dummy_064 A) (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_058 A)) (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A)) (syn_cphi (Class.cv (nb093_alpha_dummy_065 A))))))))) (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_071 r)) (Class.cab (nb093_alpha_dummy_066 r) (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_060 r)) (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r)) (syn_cphi (Class.cv (nb093_alpha_dummy_067 r))))))) (Wff.neg (Wff.classMem (Class.cv (nb093_alpha_dummy_071 r)) (Class.cab (nb093_alpha_dummy_066 r) (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_060 r)) (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r)) (syn_cphi (Class.cv (nb093_alpha_dummy_067 r))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0056 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0058 r) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0056 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0058 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0060 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0061 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0057 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0059 r) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_001 A))).fv) (by decide)) (freshVar_injective (((Class.cv r)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_058 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_059 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_060 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_061 r))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0062 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0063 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0062 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0063 r) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_065 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_067 r))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0066 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0067 r) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0066 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0067 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0064 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0065 r) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_080 A), (nb093_alpha_dummy_083 r)), ((nb093_alpha_dummy_079 A), (nb093_alpha_dummy_082 r)), ((nb093_alpha_dummy_078 A), (nb093_alpha_dummy_081 r)), ((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_070 A), (nb093_alpha_dummy_071 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_c1c) (nb093_wpp_refl_0008 A r d))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0070 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0071 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0068 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0069 r) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0074 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0075 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0072 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0073 r) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0070 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0071 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0068 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0069 r) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0074 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0075 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0072 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0073 r) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_080 A), (nb093_alpha_dummy_083 r)), ((nb093_alpha_dummy_079 A), (nb093_alpha_dummy_082 r)), ((nb093_alpha_dummy_078 A), (nb093_alpha_dummy_081 r)), ((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_070 A), (nb093_alpha_dummy_071 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_c0) (nb093_wpp_refl_0009 A r d))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0078 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0079 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0076 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0077 r) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0078 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0079 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0076 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0077 r) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0082 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0083 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0080 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0081 r) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0082 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0083 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0080 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0081 r) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0064 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0065 r) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_070 A), (nb093_alpha_dummy_071 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (nb093_wpp_refl_0010 A r d))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0064 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0065 r) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0064 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0065 r) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_070 A), (nb093_alpha_dummy_071 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (nb093_wpp_refl_0010 A r d)))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0056 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0058 r) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0056 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0058 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0060 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0061 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0057 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0059 r) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_001 A))).fv) (by decide)) (freshVar_injective (((Class.cv r)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_058 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_059 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_060 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_061 r))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0062 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0063 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0062 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0063 r) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_065 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_067 r))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0066 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0067 r) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0066 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0067 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0064 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0065 r) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_080 A), (nb093_alpha_dummy_083 r)), ((nb093_alpha_dummy_079 A), (nb093_alpha_dummy_082 r)), ((nb093_alpha_dummy_078 A), (nb093_alpha_dummy_081 r)), ((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_070 A), (nb093_alpha_dummy_071 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_c1c) (nb093_wpp_refl_0008 A r d))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0070 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0071 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0068 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0069 r) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0074 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0075 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0072 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0073 r) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0070 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0071 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0068 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0069 r) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0074 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0075 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0072 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0073 r) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_080 A), (nb093_alpha_dummy_083 r)), ((nb093_alpha_dummy_079 A), (nb093_alpha_dummy_082 r)), ((nb093_alpha_dummy_078 A), (nb093_alpha_dummy_081 r)), ((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_070 A), (nb093_alpha_dummy_071 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_c0) (nb093_wpp_refl_0009 A r d))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0078 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0079 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0076 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0077 r) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0078 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0079 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0076 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0077 r) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0082 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0083 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0080 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0081 r) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0082 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0083 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0080 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0081 r) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0064 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0065 r) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_070 A), (nb093_alpha_dummy_071 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (nb093_wpp_refl_0010 A r d))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0064 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0065 r) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0064 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0065 r) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_070 A), (nb093_alpha_dummy_071 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (nb093_wpp_refl_0010 A r d))))))))))))))))))))))))))))

theorem nb093_compact_fv_empty_0076 (A : Class) : (nb093_alpha_dummy_098 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0240 (A : Class) : (nb093_alpha_dummy_098 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_098, fv_syn_c1c] using (nb093_compact_fv_empty_0076 A)

theorem nb093_compact_fv_empty_0077 (r : Var) : (nb093_alpha_dummy_099 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0241 (r : Var) : (nb093_alpha_dummy_099 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_099, fv_syn_c1c] using (nb093_compact_fv_empty_0077 r)

theorem nb093_compact_fv_empty_0078 (A : Class) : (nb093_alpha_dummy_096 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0242 (A : Class) : (nb093_alpha_dummy_096 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_096, fv_syn_c1c] using (nb093_compact_fv_empty_0078 A)

theorem nb093_compact_fv_empty_0079 (r : Var) : (nb093_alpha_dummy_097 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0243 (r : Var) : (nb093_alpha_dummy_097 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_097, fv_syn_c1c] using (nb093_compact_fv_empty_0079 r)

theorem nb093_compact_fv_empty_0080 (A : Class) : (nb093_alpha_dummy_094 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0244 (A : Class) : (nb093_alpha_dummy_094 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_094, fv_syn_c1c] using (nb093_compact_fv_empty_0080 A)

theorem nb093_compact_fv_empty_0081 (r : Var) : (nb093_alpha_dummy_095 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0245 (r : Var) : (nb093_alpha_dummy_095 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_095, fv_syn_c1c] using (nb093_compact_fv_empty_0081 r)

theorem nb093_compact_envfresh_0011 (A : Class) (r : Var) (d : Var) : TEnvFresh [((nb093_alpha_dummy_080 A), (nb093_alpha_dummy_083 r)), ((nb093_alpha_dummy_079 A), (nb093_alpha_dummy_082 r)), ((nb093_alpha_dummy_078 A), (nb093_alpha_dummy_081 r)), ((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_098 A), (nb093_alpha_dummy_099 r)), ((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb093_alpha_dummy_080 A) (nb093_alpha_dummy_083 r) (nb093_wpp_notmem_0126 A) (nb093_wpp_notmem_0127 r) (TEnvFresh.consFresh (nb093_alpha_dummy_079 A) (nb093_alpha_dummy_082 r) (nb093_wpp_notmem_0128 A) (nb093_wpp_notmem_0129 r) (TEnvFresh.consFresh (nb093_alpha_dummy_078 A) (nb093_alpha_dummy_081 r) (nb093_wpp_notmem_0130 A) (nb093_wpp_notmem_0131 r) (TEnvFresh.consFresh (nb093_alpha_dummy_076 A) (nb093_alpha_dummy_077 r) (nb093_wpp_notmem_0132 A) (nb093_wpp_notmem_0133 r) (TEnvFresh.consFresh (nb093_alpha_dummy_072 A) (nb093_alpha_dummy_074 r) (nb093_wpp_notmem_0134 A) (nb093_wpp_notmem_0135 r) (TEnvFresh.consFresh (nb093_alpha_dummy_073 A) (nb093_alpha_dummy_075 r) (nb093_wpp_notmem_0136 A) (nb093_wpp_notmem_0137 r) (TEnvFresh.consFresh (nb093_alpha_dummy_098 A) (nb093_alpha_dummy_099 r) (nb093_wpp_notmem_0240 A) (nb093_wpp_notmem_0241 r) (TEnvFresh.consFresh (nb093_alpha_dummy_096 A) (nb093_alpha_dummy_097 r) (nb093_wpp_notmem_0242 A) (nb093_wpp_notmem_0243 r) (TEnvFresh.consFresh (nb093_alpha_dummy_065 A) (nb093_alpha_dummy_067 r) (nb093_wpp_notmem_0138 A) (nb093_wpp_notmem_0139 r) (TEnvFresh.consFresh (nb093_alpha_dummy_064 A) (nb093_alpha_dummy_066 r) (nb093_wpp_notmem_0140 A) (nb093_wpp_notmem_0141 r) (TEnvFresh.consFresh (nb093_alpha_dummy_094 A) (nb093_alpha_dummy_095 r) (nb093_wpp_notmem_0244 A) (nb093_wpp_notmem_0245 r) (TEnvFresh.consFresh (nb093_alpha_dummy_068 A) (nb093_alpha_dummy_069 r) (nb093_wpp_notmem_0144 A) (nb093_wpp_notmem_0145 r) (TEnvFresh.consFresh (nb093_alpha_dummy_059 A) (nb093_alpha_dummy_061 r) (nb093_wpp_notmem_0146 A) (nb093_wpp_notmem_0147 r) (TEnvFresh.consFresh (nb093_alpha_dummy_058 A) (nb093_alpha_dummy_060 r) (nb093_wpp_notmem_0148 A) (nb093_wpp_notmem_0149 r) (TEnvFresh.consFresh (nb093_alpha_dummy_062 A) (nb093_alpha_dummy_063 r) (nb093_wpp_notmem_0150 A) (nb093_wpp_notmem_0151 r) (TEnvFresh.consFresh (nb093_alpha_dummy_056 A) (nb093_alpha_dummy_057 r) (nb093_wpp_notmem_0152 A) (nb093_wpp_notmem_0153 r) (TEnvFresh.consFresh (nb093_alpha_dummy_054 A) (nb093_alpha_dummy_055 r) (nb093_wpp_notmem_0154 A) (nb093_wpp_notmem_0155 r) (TEnvFresh.consFresh (nb093_alpha_dummy_052 A) (nb093_alpha_dummy_053 r) (nb093_wpp_notmem_0156 A) (nb093_wpp_notmem_0157 r) (TEnvFresh.consFresh (nb093_alpha_dummy_045 A) (nb093_alpha_dummy_047 r d) (nb093_wpp_notmem_0158 A) (nb093_wpp_notmem_0159 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_044 A) (nb093_alpha_dummy_046 r d) (nb093_wpp_notmem_0160 A) (nb093_wpp_notmem_0161 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_050 A) (nb093_alpha_dummy_051 r d) (nb093_wpp_notmem_0162 A) (nb093_wpp_notmem_0163 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_048 A) (nb093_alpha_dummy_049 r d) (nb093_wpp_notmem_0164 A) (nb093_wpp_notmem_0165 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_000 A) d (nb093_wpp_notmem_0024 A) (nb093_wpp_notmem_0025 d) (TEnvFresh.consFresh (nb093_alpha_dummy_001 A) r (nb093_wpp_notmem_0026 A) (nb093_wpp_notmem_0027 r) (TEnvFresh.consFresh (nb093_alpha_dummy_006 A) (nb093_alpha_dummy_007 r d) (nb093_wpp_notmem_0028 A) (nb093_wpp_notmem_0029 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_004 A) (nb093_alpha_dummy_005 A r d) (nb093_wpp_notmem_0030 A) (nb093_wpp_notmem_0031 A r d) (TEnvFresh.consFresh (nb093_alpha_dummy_002 A) (nb093_alpha_dummy_003 A r d) (nb093_wpp_notmem_0032 A) (nb093_wpp_notmem_0033 A r d) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))))))))))

noncomputable def nb093_wpp_refl_0011 (A : Class) (r : Var) (d : Var) : TReflOn [((nb093_alpha_dummy_080 A), (nb093_alpha_dummy_083 r)), ((nb093_alpha_dummy_079 A), (nb093_alpha_dummy_082 r)), ((nb093_alpha_dummy_078 A), (nb093_alpha_dummy_081 r)), ((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_098 A), (nb093_alpha_dummy_099 r)), ((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb093_compact_envfresh_0011 A r d)

theorem nb093_wpp_notmem_0246 (A : Class) : (nb093_alpha_dummy_098 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_098, fv_syn_c0] using (nb093_compact_fv_empty_0076 A)

theorem nb093_wpp_notmem_0247 (r : Var) : (nb093_alpha_dummy_099 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_099, fv_syn_c0] using (nb093_compact_fv_empty_0077 r)

theorem nb093_wpp_notmem_0248 (A : Class) : (nb093_alpha_dummy_096 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_096, fv_syn_c0] using (nb093_compact_fv_empty_0078 A)

theorem nb093_wpp_notmem_0249 (r : Var) : (nb093_alpha_dummy_097 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_097, fv_syn_c0] using (nb093_compact_fv_empty_0079 r)

theorem nb093_wpp_notmem_0250 (A : Class) : (nb093_alpha_dummy_094 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_094, fv_syn_c0] using (nb093_compact_fv_empty_0080 A)

theorem nb093_wpp_notmem_0251 (r : Var) : (nb093_alpha_dummy_095 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_095, fv_syn_c0] using (nb093_compact_fv_empty_0081 r)

theorem nb093_compact_envfresh_0012 (A : Class) (r : Var) (d : Var) : TEnvFresh [((nb093_alpha_dummy_080 A), (nb093_alpha_dummy_083 r)), ((nb093_alpha_dummy_079 A), (nb093_alpha_dummy_082 r)), ((nb093_alpha_dummy_078 A), (nb093_alpha_dummy_081 r)), ((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_098 A), (nb093_alpha_dummy_099 r)), ((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb093_alpha_dummy_080 A) (nb093_alpha_dummy_083 r) (nb093_wpp_notmem_0166 A) (nb093_wpp_notmem_0167 r) (TEnvFresh.consFresh (nb093_alpha_dummy_079 A) (nb093_alpha_dummy_082 r) (nb093_wpp_notmem_0168 A) (nb093_wpp_notmem_0169 r) (TEnvFresh.consFresh (nb093_alpha_dummy_078 A) (nb093_alpha_dummy_081 r) (nb093_wpp_notmem_0170 A) (nb093_wpp_notmem_0171 r) (TEnvFresh.consFresh (nb093_alpha_dummy_076 A) (nb093_alpha_dummy_077 r) (nb093_wpp_notmem_0172 A) (nb093_wpp_notmem_0173 r) (TEnvFresh.consFresh (nb093_alpha_dummy_072 A) (nb093_alpha_dummy_074 r) (nb093_wpp_notmem_0174 A) (nb093_wpp_notmem_0175 r) (TEnvFresh.consFresh (nb093_alpha_dummy_073 A) (nb093_alpha_dummy_075 r) (nb093_wpp_notmem_0176 A) (nb093_wpp_notmem_0177 r) (TEnvFresh.consFresh (nb093_alpha_dummy_098 A) (nb093_alpha_dummy_099 r) (nb093_wpp_notmem_0246 A) (nb093_wpp_notmem_0247 r) (TEnvFresh.consFresh (nb093_alpha_dummy_096 A) (nb093_alpha_dummy_097 r) (nb093_wpp_notmem_0248 A) (nb093_wpp_notmem_0249 r) (TEnvFresh.consFresh (nb093_alpha_dummy_065 A) (nb093_alpha_dummy_067 r) (nb093_wpp_notmem_0178 A) (nb093_wpp_notmem_0179 r) (TEnvFresh.consFresh (nb093_alpha_dummy_064 A) (nb093_alpha_dummy_066 r) (nb093_wpp_notmem_0180 A) (nb093_wpp_notmem_0181 r) (TEnvFresh.consFresh (nb093_alpha_dummy_094 A) (nb093_alpha_dummy_095 r) (nb093_wpp_notmem_0250 A) (nb093_wpp_notmem_0251 r) (TEnvFresh.consFresh (nb093_alpha_dummy_068 A) (nb093_alpha_dummy_069 r) (nb093_wpp_notmem_0184 A) (nb093_wpp_notmem_0185 r) (TEnvFresh.consFresh (nb093_alpha_dummy_059 A) (nb093_alpha_dummy_061 r) (nb093_wpp_notmem_0186 A) (nb093_wpp_notmem_0187 r) (TEnvFresh.consFresh (nb093_alpha_dummy_058 A) (nb093_alpha_dummy_060 r) (nb093_wpp_notmem_0188 A) (nb093_wpp_notmem_0189 r) (TEnvFresh.consFresh (nb093_alpha_dummy_062 A) (nb093_alpha_dummy_063 r) (nb093_wpp_notmem_0190 A) (nb093_wpp_notmem_0191 r) (TEnvFresh.consFresh (nb093_alpha_dummy_056 A) (nb093_alpha_dummy_057 r) (nb093_wpp_notmem_0192 A) (nb093_wpp_notmem_0193 r) (TEnvFresh.consFresh (nb093_alpha_dummy_054 A) (nb093_alpha_dummy_055 r) (nb093_wpp_notmem_0194 A) (nb093_wpp_notmem_0195 r) (TEnvFresh.consFresh (nb093_alpha_dummy_052 A) (nb093_alpha_dummy_053 r) (nb093_wpp_notmem_0196 A) (nb093_wpp_notmem_0197 r) (TEnvFresh.consFresh (nb093_alpha_dummy_045 A) (nb093_alpha_dummy_047 r d) (nb093_wpp_notmem_0198 A) (nb093_wpp_notmem_0199 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_044 A) (nb093_alpha_dummy_046 r d) (nb093_wpp_notmem_0200 A) (nb093_wpp_notmem_0201 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_050 A) (nb093_alpha_dummy_051 r d) (nb093_wpp_notmem_0202 A) (nb093_wpp_notmem_0203 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_048 A) (nb093_alpha_dummy_049 r d) (nb093_wpp_notmem_0204 A) (nb093_wpp_notmem_0205 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_000 A) d (nb093_wpp_notmem_0054 A) (nb093_wpp_notmem_0055 d) (TEnvFresh.consFresh (nb093_alpha_dummy_001 A) r (nb093_wpp_notmem_0056 A) (nb093_wpp_notmem_0057 r) (TEnvFresh.consFresh (nb093_alpha_dummy_006 A) (nb093_alpha_dummy_007 r d) (nb093_wpp_notmem_0058 A) (nb093_wpp_notmem_0059 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_004 A) (nb093_alpha_dummy_005 A r d) (nb093_wpp_notmem_0060 A) (nb093_wpp_notmem_0061 A r d) (TEnvFresh.consFresh (nb093_alpha_dummy_002 A) (nb093_alpha_dummy_003 A r d) (nb093_wpp_notmem_0062 A) (nb093_wpp_notmem_0063 A r d) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))))))))))

noncomputable def nb093_wpp_refl_0012 (A : Class) (r : Var) (d : Var) : TReflOn [((nb093_alpha_dummy_080 A), (nb093_alpha_dummy_083 r)), ((nb093_alpha_dummy_079 A), (nb093_alpha_dummy_082 r)), ((nb093_alpha_dummy_078 A), (nb093_alpha_dummy_081 r)), ((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_098 A), (nb093_alpha_dummy_099 r)), ((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb093_compact_envfresh_0012 A r d)

theorem nb093_wpp_notmem_0252 (A : Class) : (nb093_alpha_dummy_098 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_098, fv_syn_cnnc] using (nb093_compact_fv_empty_0076 A)

theorem nb093_wpp_notmem_0253 (r : Var) : (nb093_alpha_dummy_099 r) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_099, fv_syn_cnnc] using (nb093_compact_fv_empty_0077 r)

theorem nb093_wpp_notmem_0254 (A : Class) : (nb093_alpha_dummy_096 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_096, fv_syn_cnnc] using (nb093_compact_fv_empty_0078 A)

theorem nb093_wpp_notmem_0255 (r : Var) : (nb093_alpha_dummy_097 r) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_097, fv_syn_cnnc] using (nb093_compact_fv_empty_0079 r)

theorem nb093_wpp_notmem_0256 (A : Class) : (nb093_alpha_dummy_094 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_094, fv_syn_cnnc] using (nb093_compact_fv_empty_0080 A)

theorem nb093_wpp_notmem_0257 (r : Var) : (nb093_alpha_dummy_095 r) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_095, fv_syn_cnnc] using (nb093_compact_fv_empty_0081 r)

theorem nb093_compact_envfresh_0013 (A : Class) (r : Var) (d : Var) : TEnvFresh [((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_098 A), (nb093_alpha_dummy_099 r)), ((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb093_alpha_dummy_076 A) (nb093_alpha_dummy_077 r) (nb093_wpp_notmem_0206 A) (nb093_wpp_notmem_0207 r) (TEnvFresh.consFresh (nb093_alpha_dummy_072 A) (nb093_alpha_dummy_074 r) (nb093_wpp_notmem_0208 A) (nb093_wpp_notmem_0209 r) (TEnvFresh.consFresh (nb093_alpha_dummy_073 A) (nb093_alpha_dummy_075 r) (nb093_wpp_notmem_0210 A) (nb093_wpp_notmem_0211 r) (TEnvFresh.consFresh (nb093_alpha_dummy_098 A) (nb093_alpha_dummy_099 r) (nb093_wpp_notmem_0252 A) (nb093_wpp_notmem_0253 r) (TEnvFresh.consFresh (nb093_alpha_dummy_096 A) (nb093_alpha_dummy_097 r) (nb093_wpp_notmem_0254 A) (nb093_wpp_notmem_0255 r) (TEnvFresh.consFresh (nb093_alpha_dummy_065 A) (nb093_alpha_dummy_067 r) (nb093_wpp_notmem_0212 A) (nb093_wpp_notmem_0213 r) (TEnvFresh.consFresh (nb093_alpha_dummy_064 A) (nb093_alpha_dummy_066 r) (nb093_wpp_notmem_0214 A) (nb093_wpp_notmem_0215 r) (TEnvFresh.consFresh (nb093_alpha_dummy_094 A) (nb093_alpha_dummy_095 r) (nb093_wpp_notmem_0256 A) (nb093_wpp_notmem_0257 r) (TEnvFresh.consFresh (nb093_alpha_dummy_068 A) (nb093_alpha_dummy_069 r) (nb093_wpp_notmem_0218 A) (nb093_wpp_notmem_0219 r) (TEnvFresh.consFresh (nb093_alpha_dummy_059 A) (nb093_alpha_dummy_061 r) (nb093_wpp_notmem_0220 A) (nb093_wpp_notmem_0221 r) (TEnvFresh.consFresh (nb093_alpha_dummy_058 A) (nb093_alpha_dummy_060 r) (nb093_wpp_notmem_0222 A) (nb093_wpp_notmem_0223 r) (TEnvFresh.consFresh (nb093_alpha_dummy_062 A) (nb093_alpha_dummy_063 r) (nb093_wpp_notmem_0224 A) (nb093_wpp_notmem_0225 r) (TEnvFresh.consFresh (nb093_alpha_dummy_056 A) (nb093_alpha_dummy_057 r) (nb093_wpp_notmem_0226 A) (nb093_wpp_notmem_0227 r) (TEnvFresh.consFresh (nb093_alpha_dummy_054 A) (nb093_alpha_dummy_055 r) (nb093_wpp_notmem_0228 A) (nb093_wpp_notmem_0229 r) (TEnvFresh.consFresh (nb093_alpha_dummy_052 A) (nb093_alpha_dummy_053 r) (nb093_wpp_notmem_0230 A) (nb093_wpp_notmem_0231 r) (TEnvFresh.consFresh (nb093_alpha_dummy_045 A) (nb093_alpha_dummy_047 r d) (nb093_wpp_notmem_0232 A) (nb093_wpp_notmem_0233 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_044 A) (nb093_alpha_dummy_046 r d) (nb093_wpp_notmem_0234 A) (nb093_wpp_notmem_0235 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_050 A) (nb093_alpha_dummy_051 r d) (nb093_wpp_notmem_0236 A) (nb093_wpp_notmem_0237 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_048 A) (nb093_alpha_dummy_049 r d) (nb093_wpp_notmem_0238 A) (nb093_wpp_notmem_0239 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_000 A) d (nb093_wpp_notmem_0078 A) (nb093_wpp_notmem_0079 d) (TEnvFresh.consFresh (nb093_alpha_dummy_001 A) r (nb093_wpp_notmem_0080 A) (nb093_wpp_notmem_0081 r) (TEnvFresh.consFresh (nb093_alpha_dummy_006 A) (nb093_alpha_dummy_007 r d) (nb093_wpp_notmem_0082 A) (nb093_wpp_notmem_0083 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_004 A) (nb093_alpha_dummy_005 A r d) (nb093_wpp_notmem_0084 A) (nb093_wpp_notmem_0085 A r d) (TEnvFresh.consFresh (nb093_alpha_dummy_002 A) (nb093_alpha_dummy_003 A r d) (nb093_wpp_notmem_0086 A) (nb093_wpp_notmem_0087 A r d) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))))))))))

noncomputable def nb093_wpp_refl_0013 (A : Class) (r : Var) (d : Var) : TReflOn [((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_098 A), (nb093_alpha_dummy_099 r)), ((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb093_compact_envfresh_0013 A r d)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

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

noncomputable def nb093_split_alpha_0003 (A : Class) (r : Var) (d : Var) : TAlphaWff [((nb093_alpha_dummy_098 A), (nb093_alpha_dummy_099 r)), ((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_098 A)) (syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))) (Wff.neg (Wff.classMem (Class.cv (nb093_alpha_dummy_098 A)) (syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))))) (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_099 r)) (syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))) (Wff.neg (Wff.classMem (Class.cv (nb093_alpha_dummy_099 r)) (syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0062 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0063 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0062 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0063 r) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0092 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0093 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0090 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0091 r) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_065 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_067 r))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0066 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0067 r) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0066 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0067 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0064 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0065 r) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_080 A), (nb093_alpha_dummy_083 r)), ((nb093_alpha_dummy_079 A), (nb093_alpha_dummy_082 r)), ((nb093_alpha_dummy_078 A), (nb093_alpha_dummy_081 r)), ((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_098 A), (nb093_alpha_dummy_099 r)), ((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_c1c) (nb093_wpp_refl_0011 A r d))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0070 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0071 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0068 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0069 r) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0074 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0075 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0072 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0073 r) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0070 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0071 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0068 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0069 r) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0074 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0075 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0072 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0073 r) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_080 A), (nb093_alpha_dummy_083 r)), ((nb093_alpha_dummy_079 A), (nb093_alpha_dummy_082 r)), ((nb093_alpha_dummy_078 A), (nb093_alpha_dummy_081 r)), ((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_098 A), (nb093_alpha_dummy_099 r)), ((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_c0) (nb093_wpp_refl_0012 A r d))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0078 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0079 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0076 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0077 r) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0078 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0079 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0076 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0077 r) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0082 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0083 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0080 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0081 r) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0082 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0083 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0080 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0081 r) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0064 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0065 r) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_098 A), (nb093_alpha_dummy_099 r)), ((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (nb093_wpp_refl_0013 A r d))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0064 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0065 r) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0064 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0065 r) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_098 A), (nb093_alpha_dummy_099 r)), ((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (nb093_wpp_refl_0013 A r d)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0062 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0063 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0062 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0063 r) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0092 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0093 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0090 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0091 r) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_065 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_067 r))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0066 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0067 r) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0066 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0067 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0064 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0065 r) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_080 A), (nb093_alpha_dummy_083 r)), ((nb093_alpha_dummy_079 A), (nb093_alpha_dummy_082 r)), ((nb093_alpha_dummy_078 A), (nb093_alpha_dummy_081 r)), ((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_098 A), (nb093_alpha_dummy_099 r)), ((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_c1c) (nb093_wpp_refl_0011 A r d))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0070 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0071 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0068 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0069 r) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0074 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0075 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0072 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0073 r) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0070 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0071 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0068 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0069 r) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0074 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0075 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0072 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0073 r) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_080 A), (nb093_alpha_dummy_083 r)), ((nb093_alpha_dummy_079 A), (nb093_alpha_dummy_082 r)), ((nb093_alpha_dummy_078 A), (nb093_alpha_dummy_081 r)), ((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_098 A), (nb093_alpha_dummy_099 r)), ((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_c0) (nb093_wpp_refl_0012 A r d))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0078 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0079 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0076 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0077 r) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0078 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0079 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0076 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0077 r) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0082 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0083 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0080 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0081 r) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0082 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0083 r) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0080 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0081 r) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0064 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0065 r) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_098 A), (nb093_alpha_dummy_099 r)), ((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (nb093_wpp_refl_0013 A r d))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0064 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0065 r) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0064 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0065 r) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_098 A), (nb093_alpha_dummy_099 r)), ((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (nb093_wpp_refl_0013 A r d))))))))))))))))))))

theorem nb093_wpp_notmem_0258 (A : Class) : (nb093_alpha_dummy_096 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_096, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0078 A)

theorem nb093_wpp_notmem_0259 (r : Var) : (nb093_alpha_dummy_097 r) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_097, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0079 r)

theorem nb093_wpp_notmem_0260 (A : Class) : (nb093_alpha_dummy_065 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_065, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0048 A)

theorem nb093_wpp_notmem_0261 (r : Var) : (nb093_alpha_dummy_067 r) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_067, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0049 r)

theorem nb093_wpp_notmem_0262 (A : Class) : (nb093_alpha_dummy_064 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_064, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0050 A)

theorem nb093_wpp_notmem_0263 (r : Var) : (nb093_alpha_dummy_066 r) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_066, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0051 r)

theorem nb093_wpp_notmem_0264 (A : Class) : (nb093_alpha_dummy_094 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_094, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0080 A)

theorem nb093_wpp_notmem_0265 (r : Var) : (nb093_alpha_dummy_095 r) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_095, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0081 r)

theorem nb093_wpp_notmem_0266 (A : Class) : (nb093_alpha_dummy_068 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_068, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0054 A)

theorem nb093_wpp_notmem_0267 (r : Var) : (nb093_alpha_dummy_069 r) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_069, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0055 r)

theorem nb093_wpp_notmem_0268 (A : Class) : (nb093_alpha_dummy_059 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_059, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0056 A)

theorem nb093_wpp_notmem_0269 (r : Var) : (nb093_alpha_dummy_061 r) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_061, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0057 r)

theorem nb093_wpp_notmem_0270 (A : Class) : (nb093_alpha_dummy_058 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_058, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0058 A)

theorem nb093_wpp_notmem_0271 (r : Var) : (nb093_alpha_dummy_060 r) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_060, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0059 r)

theorem nb093_wpp_notmem_0272 (A : Class) : (nb093_alpha_dummy_062 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_062, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0060 A)

theorem nb093_wpp_notmem_0273 (r : Var) : (nb093_alpha_dummy_063 r) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_063, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0061 r)

theorem nb093_wpp_notmem_0274 (A : Class) : (nb093_alpha_dummy_056 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_056, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0062 A)

theorem nb093_wpp_notmem_0275 (r : Var) : (nb093_alpha_dummy_057 r) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_057, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0063 r)

theorem nb093_wpp_notmem_0276 (A : Class) : (nb093_alpha_dummy_054 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_054, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0064 A)

theorem nb093_wpp_notmem_0277 (r : Var) : (nb093_alpha_dummy_055 r) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_055, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0065 r)

theorem nb093_wpp_notmem_0278 (A : Class) : (nb093_alpha_dummy_052 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_052, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0066 A)

theorem nb093_wpp_notmem_0279 (r : Var) : (nb093_alpha_dummy_053 r) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_053, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0067 r)

theorem nb093_wpp_notmem_0280 (A : Class) : (nb093_alpha_dummy_045 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_045, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0068 A)

theorem nb093_wpp_notmem_0281 (r : Var) (d : Var) : (nb093_alpha_dummy_047 r d) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_047, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0069 r d)

theorem nb093_wpp_notmem_0282 (A : Class) : (nb093_alpha_dummy_044 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_044, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0070 A)

theorem nb093_wpp_notmem_0283 (r : Var) (d : Var) : (nb093_alpha_dummy_046 r d) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_046, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0071 r d)

theorem nb093_wpp_notmem_0284 (A : Class) : (nb093_alpha_dummy_050 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_050, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0072 A)

theorem nb093_wpp_notmem_0285 (r : Var) (d : Var) : (nb093_alpha_dummy_051 r d) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_051, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0073 r d)

theorem nb093_wpp_notmem_0286 (A : Class) : (nb093_alpha_dummy_048 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_048, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0074 A)

theorem nb093_wpp_notmem_0287 (r : Var) (d : Var) : (nb093_alpha_dummy_049 r d) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_049, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0075 r d)

theorem nb093_compact_envfresh_0014 (A : Class) (r : Var) (d : Var) : TEnvFresh [((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb093_alpha_dummy_096 A) (nb093_alpha_dummy_097 r) (nb093_wpp_notmem_0258 A) (nb093_wpp_notmem_0259 r) (TEnvFresh.consFresh (nb093_alpha_dummy_065 A) (nb093_alpha_dummy_067 r) (nb093_wpp_notmem_0260 A) (nb093_wpp_notmem_0261 r) (TEnvFresh.consFresh (nb093_alpha_dummy_064 A) (nb093_alpha_dummy_066 r) (nb093_wpp_notmem_0262 A) (nb093_wpp_notmem_0263 r) (TEnvFresh.consFresh (nb093_alpha_dummy_094 A) (nb093_alpha_dummy_095 r) (nb093_wpp_notmem_0264 A) (nb093_wpp_notmem_0265 r) (TEnvFresh.consFresh (nb093_alpha_dummy_068 A) (nb093_alpha_dummy_069 r) (nb093_wpp_notmem_0266 A) (nb093_wpp_notmem_0267 r) (TEnvFresh.consFresh (nb093_alpha_dummy_059 A) (nb093_alpha_dummy_061 r) (nb093_wpp_notmem_0268 A) (nb093_wpp_notmem_0269 r) (TEnvFresh.consFresh (nb093_alpha_dummy_058 A) (nb093_alpha_dummy_060 r) (nb093_wpp_notmem_0270 A) (nb093_wpp_notmem_0271 r) (TEnvFresh.consFresh (nb093_alpha_dummy_062 A) (nb093_alpha_dummy_063 r) (nb093_wpp_notmem_0272 A) (nb093_wpp_notmem_0273 r) (TEnvFresh.consFresh (nb093_alpha_dummy_056 A) (nb093_alpha_dummy_057 r) (nb093_wpp_notmem_0274 A) (nb093_wpp_notmem_0275 r) (TEnvFresh.consFresh (nb093_alpha_dummy_054 A) (nb093_alpha_dummy_055 r) (nb093_wpp_notmem_0276 A) (nb093_wpp_notmem_0277 r) (TEnvFresh.consFresh (nb093_alpha_dummy_052 A) (nb093_alpha_dummy_053 r) (nb093_wpp_notmem_0278 A) (nb093_wpp_notmem_0279 r) (TEnvFresh.consFresh (nb093_alpha_dummy_045 A) (nb093_alpha_dummy_047 r d) (nb093_wpp_notmem_0280 A) (nb093_wpp_notmem_0281 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_044 A) (nb093_alpha_dummy_046 r d) (nb093_wpp_notmem_0282 A) (nb093_wpp_notmem_0283 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_050 A) (nb093_alpha_dummy_051 r d) (nb093_wpp_notmem_0284 A) (nb093_wpp_notmem_0285 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_048 A) (nb093_alpha_dummy_049 r d) (nb093_wpp_notmem_0286 A) (nb093_wpp_notmem_0287 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_000 A) d (nb093_wpp_notmem_0116 A) (nb093_wpp_notmem_0117 d) (TEnvFresh.consFresh (nb093_alpha_dummy_001 A) r (nb093_wpp_notmem_0118 A) (nb093_wpp_notmem_0119 r) (TEnvFresh.consFresh (nb093_alpha_dummy_006 A) (nb093_alpha_dummy_007 r d) (nb093_wpp_notmem_0120 A) (nb093_wpp_notmem_0121 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_004 A) (nb093_alpha_dummy_005 A r d) (nb093_wpp_notmem_0122 A) (nb093_wpp_notmem_0123 A r d) (TEnvFresh.consFresh (nb093_alpha_dummy_002 A) (nb093_alpha_dummy_003 A r d) (nb093_wpp_notmem_0124 A) (nb093_wpp_notmem_0125 A r d) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))))))))))))

noncomputable def nb093_wpp_refl_0014 (A : Class) (r : Var) (d : Var) : TReflOn [((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb093_compact_envfresh_0014 A r d)

theorem nb093_compact_fv_empty_0082 (A : Class) : (nb093_alpha_dummy_116 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0288 (A : Class) : (nb093_alpha_dummy_116 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_116, fv_syn_c1c] using (nb093_compact_fv_empty_0082 A)

theorem nb093_compact_fv_empty_0083 (r : Var) : (nb093_alpha_dummy_119 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0289 (r : Var) : (nb093_alpha_dummy_119 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_119, fv_syn_c1c] using (nb093_compact_fv_empty_0083 r)

theorem nb093_compact_fv_empty_0084 (A : Class) : (nb093_alpha_dummy_115 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0290 (A : Class) : (nb093_alpha_dummy_115 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_115, fv_syn_c1c] using (nb093_compact_fv_empty_0084 A)

theorem nb093_compact_fv_empty_0085 (r : Var) : (nb093_alpha_dummy_118 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0291 (r : Var) : (nb093_alpha_dummy_118 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_118, fv_syn_c1c] using (nb093_compact_fv_empty_0085 r)

theorem nb093_compact_fv_empty_0086 (A : Class) : (nb093_alpha_dummy_114 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0292 (A : Class) : (nb093_alpha_dummy_114 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_114, fv_syn_c1c] using (nb093_compact_fv_empty_0086 A)

theorem nb093_compact_fv_empty_0087 (r : Var) : (nb093_alpha_dummy_117 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0293 (r : Var) : (nb093_alpha_dummy_117 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_117, fv_syn_c1c] using (nb093_compact_fv_empty_0087 r)

theorem nb093_compact_fv_empty_0088 (A : Class) : (nb093_alpha_dummy_112 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0294 (A : Class) : (nb093_alpha_dummy_112 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_112, fv_syn_c1c] using (nb093_compact_fv_empty_0088 A)

theorem nb093_compact_fv_empty_0089 (r : Var) : (nb093_alpha_dummy_113 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0295 (r : Var) : (nb093_alpha_dummy_113 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_113, fv_syn_c1c] using (nb093_compact_fv_empty_0089 r)

theorem nb093_compact_fv_empty_0090 (A : Class) : (nb093_alpha_dummy_108 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0296 (A : Class) : (nb093_alpha_dummy_108 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_108, fv_syn_c1c] using (nb093_compact_fv_empty_0090 A)

theorem nb093_compact_fv_empty_0091 (r : Var) : (nb093_alpha_dummy_110 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0297 (r : Var) : (nb093_alpha_dummy_110 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_110, fv_syn_c1c] using (nb093_compact_fv_empty_0091 r)

theorem nb093_compact_fv_empty_0092 (A : Class) : (nb093_alpha_dummy_109 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0298 (A : Class) : (nb093_alpha_dummy_109 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_109, fv_syn_c1c] using (nb093_compact_fv_empty_0092 A)

theorem nb093_compact_fv_empty_0093 (r : Var) : (nb093_alpha_dummy_111 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0299 (r : Var) : (nb093_alpha_dummy_111 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_111, fv_syn_c1c] using (nb093_compact_fv_empty_0093 r)

theorem nb093_compact_fv_empty_0094 (A : Class) : (nb093_alpha_dummy_101 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0300 (A : Class) : (nb093_alpha_dummy_101 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_101, fv_syn_c1c] using (nb093_compact_fv_empty_0094 A)

theorem nb093_compact_fv_empty_0095 (r : Var) : (nb093_alpha_dummy_103 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0301 (r : Var) : (nb093_alpha_dummy_103 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_103, fv_syn_c1c] using (nb093_compact_fv_empty_0095 r)

theorem nb093_compact_fv_empty_0096 (A : Class) : (nb093_alpha_dummy_100 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0302 (A : Class) : (nb093_alpha_dummy_100 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_100, fv_syn_c1c] using (nb093_compact_fv_empty_0096 A)

theorem nb093_compact_fv_empty_0097 (r : Var) : (nb093_alpha_dummy_102 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0303 (r : Var) : (nb093_alpha_dummy_102 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_102, fv_syn_c1c] using (nb093_compact_fv_empty_0097 r)

theorem nb093_compact_fv_empty_0098 (A : Class) : (nb093_alpha_dummy_106 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0304 (A : Class) : (nb093_alpha_dummy_106 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_106, fv_syn_c1c] using (nb093_compact_fv_empty_0098 A)

theorem nb093_compact_fv_empty_0099 (r : Var) : (nb093_alpha_dummy_107 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0305 (r : Var) : (nb093_alpha_dummy_107 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_107, fv_syn_c1c] using (nb093_compact_fv_empty_0099 r)

theorem nb093_compact_fv_empty_0100 (A : Class) : (nb093_alpha_dummy_104 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0306 (A : Class) : (nb093_alpha_dummy_104 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_104, fv_syn_c1c] using (nb093_compact_fv_empty_0100 A)

theorem nb093_compact_fv_empty_0101 (r : Var) : (nb093_alpha_dummy_105 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0307 (r : Var) : (nb093_alpha_dummy_105 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_105, fv_syn_c1c] using (nb093_compact_fv_empty_0101 r)

theorem nb093_compact_envfresh_0015 (A : Class) (r : Var) (d : Var) : TEnvFresh [((nb093_alpha_dummy_116 A), (nb093_alpha_dummy_119 r)), ((nb093_alpha_dummy_115 A), (nb093_alpha_dummy_118 r)), ((nb093_alpha_dummy_114 A), (nb093_alpha_dummy_117 r)), ((nb093_alpha_dummy_112 A), (nb093_alpha_dummy_113 r)), ((nb093_alpha_dummy_108 A), (nb093_alpha_dummy_110 r)), ((nb093_alpha_dummy_109 A), (nb093_alpha_dummy_111 r)), ((nb093_alpha_dummy_101 A), (nb093_alpha_dummy_103 r)), ((nb093_alpha_dummy_100 A), (nb093_alpha_dummy_102 r)), ((nb093_alpha_dummy_106 A), (nb093_alpha_dummy_107 r)), ((nb093_alpha_dummy_104 A), (nb093_alpha_dummy_105 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb093_alpha_dummy_116 A) (nb093_alpha_dummy_119 r) (nb093_wpp_notmem_0288 A) (nb093_wpp_notmem_0289 r) (TEnvFresh.consFresh (nb093_alpha_dummy_115 A) (nb093_alpha_dummy_118 r) (nb093_wpp_notmem_0290 A) (nb093_wpp_notmem_0291 r) (TEnvFresh.consFresh (nb093_alpha_dummy_114 A) (nb093_alpha_dummy_117 r) (nb093_wpp_notmem_0292 A) (nb093_wpp_notmem_0293 r) (TEnvFresh.consFresh (nb093_alpha_dummy_112 A) (nb093_alpha_dummy_113 r) (nb093_wpp_notmem_0294 A) (nb093_wpp_notmem_0295 r) (TEnvFresh.consFresh (nb093_alpha_dummy_108 A) (nb093_alpha_dummy_110 r) (nb093_wpp_notmem_0296 A) (nb093_wpp_notmem_0297 r) (TEnvFresh.consFresh (nb093_alpha_dummy_109 A) (nb093_alpha_dummy_111 r) (nb093_wpp_notmem_0298 A) (nb093_wpp_notmem_0299 r) (TEnvFresh.consFresh (nb093_alpha_dummy_101 A) (nb093_alpha_dummy_103 r) (nb093_wpp_notmem_0300 A) (nb093_wpp_notmem_0301 r) (TEnvFresh.consFresh (nb093_alpha_dummy_100 A) (nb093_alpha_dummy_102 r) (nb093_wpp_notmem_0302 A) (nb093_wpp_notmem_0303 r) (TEnvFresh.consFresh (nb093_alpha_dummy_106 A) (nb093_alpha_dummy_107 r) (nb093_wpp_notmem_0304 A) (nb093_wpp_notmem_0305 r) (TEnvFresh.consFresh (nb093_alpha_dummy_104 A) (nb093_alpha_dummy_105 r) (nb093_wpp_notmem_0306 A) (nb093_wpp_notmem_0307 r) (TEnvFresh.consFresh (nb093_alpha_dummy_059 A) (nb093_alpha_dummy_061 r) (nb093_wpp_notmem_0146 A) (nb093_wpp_notmem_0147 r) (TEnvFresh.consFresh (nb093_alpha_dummy_058 A) (nb093_alpha_dummy_060 r) (nb093_wpp_notmem_0148 A) (nb093_wpp_notmem_0149 r) (TEnvFresh.consFresh (nb093_alpha_dummy_062 A) (nb093_alpha_dummy_063 r) (nb093_wpp_notmem_0150 A) (nb093_wpp_notmem_0151 r) (TEnvFresh.consFresh (nb093_alpha_dummy_056 A) (nb093_alpha_dummy_057 r) (nb093_wpp_notmem_0152 A) (nb093_wpp_notmem_0153 r) (TEnvFresh.consFresh (nb093_alpha_dummy_054 A) (nb093_alpha_dummy_055 r) (nb093_wpp_notmem_0154 A) (nb093_wpp_notmem_0155 r) (TEnvFresh.consFresh (nb093_alpha_dummy_052 A) (nb093_alpha_dummy_053 r) (nb093_wpp_notmem_0156 A) (nb093_wpp_notmem_0157 r) (TEnvFresh.consFresh (nb093_alpha_dummy_045 A) (nb093_alpha_dummy_047 r d) (nb093_wpp_notmem_0158 A) (nb093_wpp_notmem_0159 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_044 A) (nb093_alpha_dummy_046 r d) (nb093_wpp_notmem_0160 A) (nb093_wpp_notmem_0161 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_050 A) (nb093_alpha_dummy_051 r d) (nb093_wpp_notmem_0162 A) (nb093_wpp_notmem_0163 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_048 A) (nb093_alpha_dummy_049 r d) (nb093_wpp_notmem_0164 A) (nb093_wpp_notmem_0165 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_000 A) d (nb093_wpp_notmem_0024 A) (nb093_wpp_notmem_0025 d) (TEnvFresh.consFresh (nb093_alpha_dummy_001 A) r (nb093_wpp_notmem_0026 A) (nb093_wpp_notmem_0027 r) (TEnvFresh.consFresh (nb093_alpha_dummy_006 A) (nb093_alpha_dummy_007 r d) (nb093_wpp_notmem_0028 A) (nb093_wpp_notmem_0029 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_004 A) (nb093_alpha_dummy_005 A r d) (nb093_wpp_notmem_0030 A) (nb093_wpp_notmem_0031 A r d) (TEnvFresh.consFresh (nb093_alpha_dummy_002 A) (nb093_alpha_dummy_003 A r d) (nb093_wpp_notmem_0032 A) (nb093_wpp_notmem_0033 A r d) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))))))))

noncomputable def nb093_wpp_refl_0015 (A : Class) (r : Var) (d : Var) : TReflOn [((nb093_alpha_dummy_116 A), (nb093_alpha_dummy_119 r)), ((nb093_alpha_dummy_115 A), (nb093_alpha_dummy_118 r)), ((nb093_alpha_dummy_114 A), (nb093_alpha_dummy_117 r)), ((nb093_alpha_dummy_112 A), (nb093_alpha_dummy_113 r)), ((nb093_alpha_dummy_108 A), (nb093_alpha_dummy_110 r)), ((nb093_alpha_dummy_109 A), (nb093_alpha_dummy_111 r)), ((nb093_alpha_dummy_101 A), (nb093_alpha_dummy_103 r)), ((nb093_alpha_dummy_100 A), (nb093_alpha_dummy_102 r)), ((nb093_alpha_dummy_106 A), (nb093_alpha_dummy_107 r)), ((nb093_alpha_dummy_104 A), (nb093_alpha_dummy_105 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb093_compact_envfresh_0015 A r d)

theorem nb093_wpp_notmem_0308 (A : Class) : (nb093_alpha_dummy_116 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_116, fv_syn_c0] using (nb093_compact_fv_empty_0082 A)

theorem nb093_wpp_notmem_0309 (r : Var) : (nb093_alpha_dummy_119 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_119, fv_syn_c0] using (nb093_compact_fv_empty_0083 r)

theorem nb093_wpp_notmem_0310 (A : Class) : (nb093_alpha_dummy_115 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_115, fv_syn_c0] using (nb093_compact_fv_empty_0084 A)

theorem nb093_wpp_notmem_0311 (r : Var) : (nb093_alpha_dummy_118 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_118, fv_syn_c0] using (nb093_compact_fv_empty_0085 r)

theorem nb093_wpp_notmem_0312 (A : Class) : (nb093_alpha_dummy_114 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_114, fv_syn_c0] using (nb093_compact_fv_empty_0086 A)

theorem nb093_wpp_notmem_0313 (r : Var) : (nb093_alpha_dummy_117 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_117, fv_syn_c0] using (nb093_compact_fv_empty_0087 r)

theorem nb093_wpp_notmem_0314 (A : Class) : (nb093_alpha_dummy_112 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_112, fv_syn_c0] using (nb093_compact_fv_empty_0088 A)

theorem nb093_wpp_notmem_0315 (r : Var) : (nb093_alpha_dummy_113 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_113, fv_syn_c0] using (nb093_compact_fv_empty_0089 r)

theorem nb093_wpp_notmem_0316 (A : Class) : (nb093_alpha_dummy_108 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_108, fv_syn_c0] using (nb093_compact_fv_empty_0090 A)

theorem nb093_wpp_notmem_0317 (r : Var) : (nb093_alpha_dummy_110 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_110, fv_syn_c0] using (nb093_compact_fv_empty_0091 r)

theorem nb093_wpp_notmem_0318 (A : Class) : (nb093_alpha_dummy_109 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_109, fv_syn_c0] using (nb093_compact_fv_empty_0092 A)

theorem nb093_wpp_notmem_0319 (r : Var) : (nb093_alpha_dummy_111 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_111, fv_syn_c0] using (nb093_compact_fv_empty_0093 r)

theorem nb093_wpp_notmem_0320 (A : Class) : (nb093_alpha_dummy_101 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_101, fv_syn_c0] using (nb093_compact_fv_empty_0094 A)

theorem nb093_wpp_notmem_0321 (r : Var) : (nb093_alpha_dummy_103 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_103, fv_syn_c0] using (nb093_compact_fv_empty_0095 r)

theorem nb093_wpp_notmem_0322 (A : Class) : (nb093_alpha_dummy_100 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_100, fv_syn_c0] using (nb093_compact_fv_empty_0096 A)

theorem nb093_wpp_notmem_0323 (r : Var) : (nb093_alpha_dummy_102 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_102, fv_syn_c0] using (nb093_compact_fv_empty_0097 r)

theorem nb093_wpp_notmem_0324 (A : Class) : (nb093_alpha_dummy_106 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_106, fv_syn_c0] using (nb093_compact_fv_empty_0098 A)

theorem nb093_wpp_notmem_0325 (r : Var) : (nb093_alpha_dummy_107 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_107, fv_syn_c0] using (nb093_compact_fv_empty_0099 r)

theorem nb093_wpp_notmem_0326 (A : Class) : (nb093_alpha_dummy_104 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_104, fv_syn_c0] using (nb093_compact_fv_empty_0100 A)

theorem nb093_wpp_notmem_0327 (r : Var) : (nb093_alpha_dummy_105 r) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_105, fv_syn_c0] using (nb093_compact_fv_empty_0101 r)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
