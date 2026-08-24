import NAR4C068C001Part014

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

theorem nb068_compact_fv_empty_0054 : (nb068_alpha_dummy_045) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0128 : (nb068_alpha_dummy_045) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_045, fv_syn_c1c] using (nb068_compact_fv_empty_0054)

theorem nb068_compact_fv_empty_0055 (f : Var) : (nb068_alpha_dummy_048 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0129 (f : Var) : (nb068_alpha_dummy_048 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_048, fv_syn_c1c] using (nb068_compact_fv_empty_0055 f)

theorem nb068_compact_fv_empty_0056 : (nb068_alpha_dummy_051) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0130 : (nb068_alpha_dummy_051) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_051, fv_syn_c1c] using (nb068_compact_fv_empty_0056)

theorem nb068_compact_fv_empty_0057 (f : Var) : (nb068_alpha_dummy_052 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0131 (f : Var) : (nb068_alpha_dummy_052 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_052, fv_syn_c1c] using (nb068_compact_fv_empty_0057 f)

theorem nb068_compact_fv_empty_0058 : (nb068_alpha_dummy_043) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0132 : (nb068_alpha_dummy_043) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_043, fv_syn_c1c] using (nb068_compact_fv_empty_0058)

theorem nb068_compact_fv_empty_0059 (f : Var) : (nb068_alpha_dummy_044 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0133 (f : Var) : (nb068_alpha_dummy_044 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_044, fv_syn_c1c] using (nb068_compact_fv_empty_0059 f)

theorem nb068_compact_fv_empty_0060 : (nb068_alpha_dummy_041) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0134 : (nb068_alpha_dummy_041) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_041, fv_syn_c1c] using (nb068_compact_fv_empty_0060)

theorem nb068_compact_fv_empty_0061 (f : Var) : (nb068_alpha_dummy_042 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0135 (f : Var) : (nb068_alpha_dummy_042 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_042, fv_syn_c1c] using (nb068_compact_fv_empty_0061 f)

theorem nb068_compact_fv_empty_0062 : (nb068_alpha_dummy_000) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0136 : (nb068_alpha_dummy_000) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_000, fv_syn_c1c] using (nb068_compact_fv_empty_0062)

theorem nb068_compact_fv_empty_0063 (f : Var) : f ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0137 (f : Var) : f ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb068_compact_fv_empty_0063 f)

theorem nb068_compact_envfresh_0007 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_069), (nb068_alpha_dummy_072 f)), ((nb068_alpha_dummy_068), (nb068_alpha_dummy_071 f)), ((nb068_alpha_dummy_067), (nb068_alpha_dummy_070 f)), ((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)), ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)), ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_059), (nb068_alpha_dummy_060 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_069) (nb068_alpha_dummy_072 f) (nb068_wpp_notmem_0106) (nb068_wpp_notmem_0107 f) (TEnvFresh.consFresh (nb068_alpha_dummy_068) (nb068_alpha_dummy_071 f) (nb068_wpp_notmem_0108) (nb068_wpp_notmem_0109 f) (TEnvFresh.consFresh (nb068_alpha_dummy_067) (nb068_alpha_dummy_070 f) (nb068_wpp_notmem_0110) (nb068_wpp_notmem_0111 f) (TEnvFresh.consFresh (nb068_alpha_dummy_065) (nb068_alpha_dummy_066 f) (nb068_wpp_notmem_0112) (nb068_wpp_notmem_0113 f) (TEnvFresh.consFresh (nb068_alpha_dummy_061) (nb068_alpha_dummy_063 f) (nb068_wpp_notmem_0114) (nb068_wpp_notmem_0115 f) (TEnvFresh.consFresh (nb068_alpha_dummy_062) (nb068_alpha_dummy_064 f) (nb068_wpp_notmem_0116) (nb068_wpp_notmem_0117 f) (TEnvFresh.consFresh (nb068_alpha_dummy_054) (nb068_alpha_dummy_056 f) (nb068_wpp_notmem_0118) (nb068_wpp_notmem_0119 f) (TEnvFresh.consFresh (nb068_alpha_dummy_053) (nb068_alpha_dummy_055 f) (nb068_wpp_notmem_0120) (nb068_wpp_notmem_0121 f) (TEnvFresh.consFresh (nb068_alpha_dummy_059) (nb068_alpha_dummy_060 f) (nb068_wpp_notmem_0122) (nb068_wpp_notmem_0123 f) (TEnvFresh.consFresh (nb068_alpha_dummy_057) (nb068_alpha_dummy_058 f) (nb068_wpp_notmem_0124) (nb068_wpp_notmem_0125 f) (TEnvFresh.consFresh (nb068_alpha_dummy_046) (nb068_alpha_dummy_049 f) (nb068_wpp_notmem_0126) (nb068_wpp_notmem_0127 f) (TEnvFresh.consFresh (nb068_alpha_dummy_045) (nb068_alpha_dummy_048 f) (nb068_wpp_notmem_0128) (nb068_wpp_notmem_0129 f) (TEnvFresh.consFresh (nb068_alpha_dummy_051) (nb068_alpha_dummy_052 f) (nb068_wpp_notmem_0130) (nb068_wpp_notmem_0131 f) (TEnvFresh.consFresh (nb068_alpha_dummy_043) (nb068_alpha_dummy_044 f) (nb068_wpp_notmem_0132) (nb068_wpp_notmem_0133 f) (TEnvFresh.consFresh (nb068_alpha_dummy_041) (nb068_alpha_dummy_042 f) (nb068_wpp_notmem_0134) (nb068_wpp_notmem_0135 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0136) (nb068_wpp_notmem_0137 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0020) (nb068_wpp_notmem_0021 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0022) (nb068_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0024) (nb068_wpp_notmem_0025 x y f) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))

noncomputable def nb068_wpp_refl_0007 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_069), (nb068_alpha_dummy_072 f)), ((nb068_alpha_dummy_068), (nb068_alpha_dummy_071 f)), ((nb068_alpha_dummy_067), (nb068_alpha_dummy_070 f)), ((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)), ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)), ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_059), (nb068_alpha_dummy_060 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0007 x y f)

theorem nb068_wpp_notmem_0138 : (nb068_alpha_dummy_069) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_069, fv_syn_c0] using (nb068_compact_fv_empty_0032)

theorem nb068_wpp_notmem_0139 (f : Var) : (nb068_alpha_dummy_072 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_072, fv_syn_c0] using (nb068_compact_fv_empty_0033 f)

theorem nb068_wpp_notmem_0140 : (nb068_alpha_dummy_068) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_068, fv_syn_c0] using (nb068_compact_fv_empty_0034)

theorem nb068_wpp_notmem_0141 (f : Var) : (nb068_alpha_dummy_071 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_071, fv_syn_c0] using (nb068_compact_fv_empty_0035 f)

theorem nb068_wpp_notmem_0142 : (nb068_alpha_dummy_067) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_067, fv_syn_c0] using (nb068_compact_fv_empty_0036)

theorem nb068_wpp_notmem_0143 (f : Var) : (nb068_alpha_dummy_070 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_070, fv_syn_c0] using (nb068_compact_fv_empty_0037 f)

theorem nb068_wpp_notmem_0144 : (nb068_alpha_dummy_065) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_065, fv_syn_c0] using (nb068_compact_fv_empty_0038)

theorem nb068_wpp_notmem_0145 (f : Var) : (nb068_alpha_dummy_066 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_066, fv_syn_c0] using (nb068_compact_fv_empty_0039 f)

theorem nb068_wpp_notmem_0146 : (nb068_alpha_dummy_061) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_061, fv_syn_c0] using (nb068_compact_fv_empty_0040)

theorem nb068_wpp_notmem_0147 (f : Var) : (nb068_alpha_dummy_063 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_063, fv_syn_c0] using (nb068_compact_fv_empty_0041 f)

theorem nb068_wpp_notmem_0148 : (nb068_alpha_dummy_062) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_062, fv_syn_c0] using (nb068_compact_fv_empty_0042)

theorem nb068_wpp_notmem_0149 (f : Var) : (nb068_alpha_dummy_064 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_064, fv_syn_c0] using (nb068_compact_fv_empty_0043 f)

theorem nb068_wpp_notmem_0150 : (nb068_alpha_dummy_054) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_054, fv_syn_c0] using (nb068_compact_fv_empty_0044)

theorem nb068_wpp_notmem_0151 (f : Var) : (nb068_alpha_dummy_056 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_056, fv_syn_c0] using (nb068_compact_fv_empty_0045 f)

theorem nb068_wpp_notmem_0152 : (nb068_alpha_dummy_053) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_053, fv_syn_c0] using (nb068_compact_fv_empty_0046)

theorem nb068_wpp_notmem_0153 (f : Var) : (nb068_alpha_dummy_055 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_055, fv_syn_c0] using (nb068_compact_fv_empty_0047 f)

theorem nb068_wpp_notmem_0154 : (nb068_alpha_dummy_059) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_059, fv_syn_c0] using (nb068_compact_fv_empty_0048)

theorem nb068_wpp_notmem_0155 (f : Var) : (nb068_alpha_dummy_060 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_060, fv_syn_c0] using (nb068_compact_fv_empty_0049 f)

theorem nb068_wpp_notmem_0156 : (nb068_alpha_dummy_057) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_057, fv_syn_c0] using (nb068_compact_fv_empty_0050)

theorem nb068_wpp_notmem_0157 (f : Var) : (nb068_alpha_dummy_058 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_058, fv_syn_c0] using (nb068_compact_fv_empty_0051 f)

theorem nb068_wpp_notmem_0158 : (nb068_alpha_dummy_046) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_046, fv_syn_c0] using (nb068_compact_fv_empty_0052)

theorem nb068_wpp_notmem_0159 (f : Var) : (nb068_alpha_dummy_049 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_049, fv_syn_c0] using (nb068_compact_fv_empty_0053 f)

theorem nb068_wpp_notmem_0160 : (nb068_alpha_dummy_045) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_045, fv_syn_c0] using (nb068_compact_fv_empty_0054)

theorem nb068_wpp_notmem_0161 (f : Var) : (nb068_alpha_dummy_048 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_048, fv_syn_c0] using (nb068_compact_fv_empty_0055 f)

theorem nb068_wpp_notmem_0162 : (nb068_alpha_dummy_051) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_051, fv_syn_c0] using (nb068_compact_fv_empty_0056)

theorem nb068_wpp_notmem_0163 (f : Var) : (nb068_alpha_dummy_052 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_052, fv_syn_c0] using (nb068_compact_fv_empty_0057 f)

theorem nb068_wpp_notmem_0164 : (nb068_alpha_dummy_043) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_043, fv_syn_c0] using (nb068_compact_fv_empty_0058)

theorem nb068_wpp_notmem_0165 (f : Var) : (nb068_alpha_dummy_044 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_044, fv_syn_c0] using (nb068_compact_fv_empty_0059 f)

theorem nb068_wpp_notmem_0166 : (nb068_alpha_dummy_041) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_041, fv_syn_c0] using (nb068_compact_fv_empty_0060)

theorem nb068_wpp_notmem_0167 (f : Var) : (nb068_alpha_dummy_042 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_042, fv_syn_c0] using (nb068_compact_fv_empty_0061 f)

theorem nb068_wpp_notmem_0168 : (nb068_alpha_dummy_000) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_000, fv_syn_c0] using (nb068_compact_fv_empty_0062)

theorem nb068_wpp_notmem_0169 (f : Var) : f ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb068_compact_fv_empty_0063 f)

theorem nb068_compact_envfresh_0008 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_069), (nb068_alpha_dummy_072 f)), ((nb068_alpha_dummy_068), (nb068_alpha_dummy_071 f)), ((nb068_alpha_dummy_067), (nb068_alpha_dummy_070 f)), ((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)), ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)), ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_059), (nb068_alpha_dummy_060 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_069) (nb068_alpha_dummy_072 f) (nb068_wpp_notmem_0138) (nb068_wpp_notmem_0139 f) (TEnvFresh.consFresh (nb068_alpha_dummy_068) (nb068_alpha_dummy_071 f) (nb068_wpp_notmem_0140) (nb068_wpp_notmem_0141 f) (TEnvFresh.consFresh (nb068_alpha_dummy_067) (nb068_alpha_dummy_070 f) (nb068_wpp_notmem_0142) (nb068_wpp_notmem_0143 f) (TEnvFresh.consFresh (nb068_alpha_dummy_065) (nb068_alpha_dummy_066 f) (nb068_wpp_notmem_0144) (nb068_wpp_notmem_0145 f) (TEnvFresh.consFresh (nb068_alpha_dummy_061) (nb068_alpha_dummy_063 f) (nb068_wpp_notmem_0146) (nb068_wpp_notmem_0147 f) (TEnvFresh.consFresh (nb068_alpha_dummy_062) (nb068_alpha_dummy_064 f) (nb068_wpp_notmem_0148) (nb068_wpp_notmem_0149 f) (TEnvFresh.consFresh (nb068_alpha_dummy_054) (nb068_alpha_dummy_056 f) (nb068_wpp_notmem_0150) (nb068_wpp_notmem_0151 f) (TEnvFresh.consFresh (nb068_alpha_dummy_053) (nb068_alpha_dummy_055 f) (nb068_wpp_notmem_0152) (nb068_wpp_notmem_0153 f) (TEnvFresh.consFresh (nb068_alpha_dummy_059) (nb068_alpha_dummy_060 f) (nb068_wpp_notmem_0154) (nb068_wpp_notmem_0155 f) (TEnvFresh.consFresh (nb068_alpha_dummy_057) (nb068_alpha_dummy_058 f) (nb068_wpp_notmem_0156) (nb068_wpp_notmem_0157 f) (TEnvFresh.consFresh (nb068_alpha_dummy_046) (nb068_alpha_dummy_049 f) (nb068_wpp_notmem_0158) (nb068_wpp_notmem_0159 f) (TEnvFresh.consFresh (nb068_alpha_dummy_045) (nb068_alpha_dummy_048 f) (nb068_wpp_notmem_0160) (nb068_wpp_notmem_0161 f) (TEnvFresh.consFresh (nb068_alpha_dummy_051) (nb068_alpha_dummy_052 f) (nb068_wpp_notmem_0162) (nb068_wpp_notmem_0163 f) (TEnvFresh.consFresh (nb068_alpha_dummy_043) (nb068_alpha_dummy_044 f) (nb068_wpp_notmem_0164) (nb068_wpp_notmem_0165 f) (TEnvFresh.consFresh (nb068_alpha_dummy_041) (nb068_alpha_dummy_042 f) (nb068_wpp_notmem_0166) (nb068_wpp_notmem_0167 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0168) (nb068_wpp_notmem_0169 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0046) (nb068_wpp_notmem_0047 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0048) (nb068_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0050) (nb068_wpp_notmem_0051 x y f) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))

noncomputable def nb068_wpp_refl_0008 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_069), (nb068_alpha_dummy_072 f)), ((nb068_alpha_dummy_068), (nb068_alpha_dummy_071 f)), ((nb068_alpha_dummy_067), (nb068_alpha_dummy_070 f)), ((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)), ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)), ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_059), (nb068_alpha_dummy_060 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0008 x y f)

noncomputable def nb068_split_alpha_0005 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_069), (nb068_alpha_dummy_072 f)), ((nb068_alpha_dummy_068), (nb068_alpha_dummy_071 f)), ((nb068_alpha_dummy_067), (nb068_alpha_dummy_070 f)), ((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)), ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)), ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_059), (nb068_alpha_dummy_060 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_068)) (Class.cv (nb068_alpha_dummy_069))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_067)) (syn_cun (Class.cv (nb068_alpha_dummy_068)) (Class.cv (nb068_alpha_dummy_069)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_071 f)) (Class.cv (nb068_alpha_dummy_072 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_070 f)) (syn_cun (Class.cv (nb068_alpha_dummy_071 f)) (Class.cv (nb068_alpha_dummy_072 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0061 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0059 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0065 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0063 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0061 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0059 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0065 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0063 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_069), (nb068_alpha_dummy_072 f)), ((nb068_alpha_dummy_068), (nb068_alpha_dummy_071 f)), ((nb068_alpha_dummy_067), (nb068_alpha_dummy_070 f)), ((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)), ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)), ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_059), (nb068_alpha_dummy_060 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c0) (nb068_wpp_refl_0008 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0069 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0067 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0069 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0067 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0073 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0071 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0073 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0071 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb068_wpp_notmem_0170 : (nb068_alpha_dummy_065) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_065, fv_syn_cnnc] using (nb068_compact_fv_empty_0038)

theorem nb068_wpp_notmem_0171 (f : Var) : (nb068_alpha_dummy_066 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_066, fv_syn_cnnc] using (nb068_compact_fv_empty_0039 f)

theorem nb068_wpp_notmem_0172 : (nb068_alpha_dummy_061) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_061, fv_syn_cnnc] using (nb068_compact_fv_empty_0040)

theorem nb068_wpp_notmem_0173 (f : Var) : (nb068_alpha_dummy_063 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_063, fv_syn_cnnc] using (nb068_compact_fv_empty_0041 f)

theorem nb068_wpp_notmem_0174 : (nb068_alpha_dummy_062) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_062, fv_syn_cnnc] using (nb068_compact_fv_empty_0042)

theorem nb068_wpp_notmem_0175 (f : Var) : (nb068_alpha_dummy_064 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_064, fv_syn_cnnc] using (nb068_compact_fv_empty_0043 f)

theorem nb068_wpp_notmem_0176 : (nb068_alpha_dummy_054) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_054, fv_syn_cnnc] using (nb068_compact_fv_empty_0044)

theorem nb068_wpp_notmem_0177 (f : Var) : (nb068_alpha_dummy_056 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_056, fv_syn_cnnc] using (nb068_compact_fv_empty_0045 f)

theorem nb068_wpp_notmem_0178 : (nb068_alpha_dummy_053) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_053, fv_syn_cnnc] using (nb068_compact_fv_empty_0046)

theorem nb068_wpp_notmem_0179 (f : Var) : (nb068_alpha_dummy_055 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_055, fv_syn_cnnc] using (nb068_compact_fv_empty_0047 f)

theorem nb068_wpp_notmem_0180 : (nb068_alpha_dummy_059) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_059, fv_syn_cnnc] using (nb068_compact_fv_empty_0048)

theorem nb068_wpp_notmem_0181 (f : Var) : (nb068_alpha_dummy_060 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_060, fv_syn_cnnc] using (nb068_compact_fv_empty_0049 f)

theorem nb068_wpp_notmem_0182 : (nb068_alpha_dummy_057) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_057, fv_syn_cnnc] using (nb068_compact_fv_empty_0050)

theorem nb068_wpp_notmem_0183 (f : Var) : (nb068_alpha_dummy_058 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_058, fv_syn_cnnc] using (nb068_compact_fv_empty_0051 f)

theorem nb068_wpp_notmem_0184 : (nb068_alpha_dummy_046) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_046, fv_syn_cnnc] using (nb068_compact_fv_empty_0052)

theorem nb068_wpp_notmem_0185 (f : Var) : (nb068_alpha_dummy_049 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_049, fv_syn_cnnc] using (nb068_compact_fv_empty_0053 f)

theorem nb068_wpp_notmem_0186 : (nb068_alpha_dummy_045) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_045, fv_syn_cnnc] using (nb068_compact_fv_empty_0054)

theorem nb068_wpp_notmem_0187 (f : Var) : (nb068_alpha_dummy_048 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_048, fv_syn_cnnc] using (nb068_compact_fv_empty_0055 f)

theorem nb068_wpp_notmem_0188 : (nb068_alpha_dummy_051) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_051, fv_syn_cnnc] using (nb068_compact_fv_empty_0056)

theorem nb068_wpp_notmem_0189 (f : Var) : (nb068_alpha_dummy_052 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_052, fv_syn_cnnc] using (nb068_compact_fv_empty_0057 f)

theorem nb068_wpp_notmem_0190 : (nb068_alpha_dummy_043) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_043, fv_syn_cnnc] using (nb068_compact_fv_empty_0058)

theorem nb068_wpp_notmem_0191 (f : Var) : (nb068_alpha_dummy_044 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_044, fv_syn_cnnc] using (nb068_compact_fv_empty_0059 f)

theorem nb068_wpp_notmem_0192 : (nb068_alpha_dummy_041) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_041, fv_syn_cnnc] using (nb068_compact_fv_empty_0060)

theorem nb068_wpp_notmem_0193 (f : Var) : (nb068_alpha_dummy_042 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_042, fv_syn_cnnc] using (nb068_compact_fv_empty_0061 f)

theorem nb068_wpp_notmem_0194 : (nb068_alpha_dummy_000) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_000, fv_syn_cnnc] using (nb068_compact_fv_empty_0062)

theorem nb068_wpp_notmem_0195 (f : Var) : f ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb068_compact_fv_empty_0063 f)

theorem nb068_compact_envfresh_0009 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)), ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)), ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_059), (nb068_alpha_dummy_060 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_065) (nb068_alpha_dummy_066 f) (nb068_wpp_notmem_0170) (nb068_wpp_notmem_0171 f) (TEnvFresh.consFresh (nb068_alpha_dummy_061) (nb068_alpha_dummy_063 f) (nb068_wpp_notmem_0172) (nb068_wpp_notmem_0173 f) (TEnvFresh.consFresh (nb068_alpha_dummy_062) (nb068_alpha_dummy_064 f) (nb068_wpp_notmem_0174) (nb068_wpp_notmem_0175 f) (TEnvFresh.consFresh (nb068_alpha_dummy_054) (nb068_alpha_dummy_056 f) (nb068_wpp_notmem_0176) (nb068_wpp_notmem_0177 f) (TEnvFresh.consFresh (nb068_alpha_dummy_053) (nb068_alpha_dummy_055 f) (nb068_wpp_notmem_0178) (nb068_wpp_notmem_0179 f) (TEnvFresh.consFresh (nb068_alpha_dummy_059) (nb068_alpha_dummy_060 f) (nb068_wpp_notmem_0180) (nb068_wpp_notmem_0181 f) (TEnvFresh.consFresh (nb068_alpha_dummy_057) (nb068_alpha_dummy_058 f) (nb068_wpp_notmem_0182) (nb068_wpp_notmem_0183 f) (TEnvFresh.consFresh (nb068_alpha_dummy_046) (nb068_alpha_dummy_049 f) (nb068_wpp_notmem_0184) (nb068_wpp_notmem_0185 f) (TEnvFresh.consFresh (nb068_alpha_dummy_045) (nb068_alpha_dummy_048 f) (nb068_wpp_notmem_0186) (nb068_wpp_notmem_0187 f) (TEnvFresh.consFresh (nb068_alpha_dummy_051) (nb068_alpha_dummy_052 f) (nb068_wpp_notmem_0188) (nb068_wpp_notmem_0189 f) (TEnvFresh.consFresh (nb068_alpha_dummy_043) (nb068_alpha_dummy_044 f) (nb068_wpp_notmem_0190) (nb068_wpp_notmem_0191 f) (TEnvFresh.consFresh (nb068_alpha_dummy_041) (nb068_alpha_dummy_042 f) (nb068_wpp_notmem_0192) (nb068_wpp_notmem_0193 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0194) (nb068_wpp_notmem_0195 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0066) (nb068_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0068) (nb068_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0070) (nb068_wpp_notmem_0071 x y f) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))

noncomputable def nb068_wpp_refl_0009 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)), ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)), ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_059), (nb068_alpha_dummy_060 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0009 x y f)

noncomputable def nb068_split_alpha_0006 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)), ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_059), (nb068_alpha_dummy_060 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_061)) (Class.cv (nb068_alpha_dummy_054))) (Wff.classEq (Class.cv (nb068_alpha_dummy_062)) (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_061)) (syn_cnnc)) (syn_cplc (Class.cv (nb068_alpha_dummy_061)) (syn_c1c)) (Class.cv (nb068_alpha_dummy_061)))))) (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_063 f)) (Class.cv (nb068_alpha_dummy_056 f))) (Wff.classEq (Class.cv (nb068_alpha_dummy_064 f)) (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_063 f)) (syn_cnnc)) (syn_cplc (Class.cv (nb068_alpha_dummy_063 f)) (syn_c1c)) (Class.cv (nb068_alpha_dummy_063 f)))))) :=
  (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0052) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0053 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0052) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0053 f) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_054))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_056 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0056) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0057 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0057 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0055 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_069), (nb068_alpha_dummy_072 f)), ((nb068_alpha_dummy_068), (nb068_alpha_dummy_071 f)), ((nb068_alpha_dummy_067), (nb068_alpha_dummy_070 f)), ((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)), ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)), ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_059), (nb068_alpha_dummy_060 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c1c) (nb068_wpp_refl_0007 x y f))) (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0005 x y f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0055 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)), ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)), ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_059), (nb068_alpha_dummy_060 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0009 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0055 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0055 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)), ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)), ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_059), (nb068_alpha_dummy_060 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0009 x y f))))))))))))))

theorem nb068_compact_fv_empty_0064 : (nb068_alpha_dummy_087) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0196 : (nb068_alpha_dummy_087) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_087, fv_syn_c1c] using (nb068_compact_fv_empty_0064)

theorem nb068_compact_fv_empty_0065 (f : Var) : (nb068_alpha_dummy_088 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0197 (f : Var) : (nb068_alpha_dummy_088 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_088, fv_syn_c1c] using (nb068_compact_fv_empty_0065 f)

theorem nb068_compact_fv_empty_0066 : (nb068_alpha_dummy_085) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0198 : (nb068_alpha_dummy_085) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_085, fv_syn_c1c] using (nb068_compact_fv_empty_0066)

theorem nb068_compact_fv_empty_0067 (f : Var) : (nb068_alpha_dummy_086 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0199 (f : Var) : (nb068_alpha_dummy_086 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_086, fv_syn_c1c] using (nb068_compact_fv_empty_0067 f)

theorem nb068_compact_fv_empty_0068 : (nb068_alpha_dummy_083) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0200 : (nb068_alpha_dummy_083) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_083, fv_syn_c1c] using (nb068_compact_fv_empty_0068)

theorem nb068_compact_fv_empty_0069 (f : Var) : (nb068_alpha_dummy_084 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0201 (f : Var) : (nb068_alpha_dummy_084 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_084, fv_syn_c1c] using (nb068_compact_fv_empty_0069 f)

theorem nb068_compact_envfresh_0010 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_069), (nb068_alpha_dummy_072 f)), ((nb068_alpha_dummy_068), (nb068_alpha_dummy_071 f)), ((nb068_alpha_dummy_067), (nb068_alpha_dummy_070 f)), ((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)), ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)), ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)), ((nb068_alpha_dummy_087), (nb068_alpha_dummy_088 f)), ((nb068_alpha_dummy_085), (nb068_alpha_dummy_086 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_069) (nb068_alpha_dummy_072 f) (nb068_wpp_notmem_0106) (nb068_wpp_notmem_0107 f) (TEnvFresh.consFresh (nb068_alpha_dummy_068) (nb068_alpha_dummy_071 f) (nb068_wpp_notmem_0108) (nb068_wpp_notmem_0109 f) (TEnvFresh.consFresh (nb068_alpha_dummy_067) (nb068_alpha_dummy_070 f) (nb068_wpp_notmem_0110) (nb068_wpp_notmem_0111 f) (TEnvFresh.consFresh (nb068_alpha_dummy_065) (nb068_alpha_dummy_066 f) (nb068_wpp_notmem_0112) (nb068_wpp_notmem_0113 f) (TEnvFresh.consFresh (nb068_alpha_dummy_061) (nb068_alpha_dummy_063 f) (nb068_wpp_notmem_0114) (nb068_wpp_notmem_0115 f) (TEnvFresh.consFresh (nb068_alpha_dummy_062) (nb068_alpha_dummy_064 f) (nb068_wpp_notmem_0116) (nb068_wpp_notmem_0117 f) (TEnvFresh.consFresh (nb068_alpha_dummy_087) (nb068_alpha_dummy_088 f) (nb068_wpp_notmem_0196) (nb068_wpp_notmem_0197 f) (TEnvFresh.consFresh (nb068_alpha_dummy_085) (nb068_alpha_dummy_086 f) (nb068_wpp_notmem_0198) (nb068_wpp_notmem_0199 f) (TEnvFresh.consFresh (nb068_alpha_dummy_054) (nb068_alpha_dummy_056 f) (nb068_wpp_notmem_0118) (nb068_wpp_notmem_0119 f) (TEnvFresh.consFresh (nb068_alpha_dummy_053) (nb068_alpha_dummy_055 f) (nb068_wpp_notmem_0120) (nb068_wpp_notmem_0121 f) (TEnvFresh.consFresh (nb068_alpha_dummy_083) (nb068_alpha_dummy_084 f) (nb068_wpp_notmem_0200) (nb068_wpp_notmem_0201 f) (TEnvFresh.consFresh (nb068_alpha_dummy_057) (nb068_alpha_dummy_058 f) (nb068_wpp_notmem_0124) (nb068_wpp_notmem_0125 f) (TEnvFresh.consFresh (nb068_alpha_dummy_046) (nb068_alpha_dummy_049 f) (nb068_wpp_notmem_0126) (nb068_wpp_notmem_0127 f) (TEnvFresh.consFresh (nb068_alpha_dummy_045) (nb068_alpha_dummy_048 f) (nb068_wpp_notmem_0128) (nb068_wpp_notmem_0129 f) (TEnvFresh.consFresh (nb068_alpha_dummy_051) (nb068_alpha_dummy_052 f) (nb068_wpp_notmem_0130) (nb068_wpp_notmem_0131 f) (TEnvFresh.consFresh (nb068_alpha_dummy_043) (nb068_alpha_dummy_044 f) (nb068_wpp_notmem_0132) (nb068_wpp_notmem_0133 f) (TEnvFresh.consFresh (nb068_alpha_dummy_041) (nb068_alpha_dummy_042 f) (nb068_wpp_notmem_0134) (nb068_wpp_notmem_0135 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0136) (nb068_wpp_notmem_0137 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0020) (nb068_wpp_notmem_0021 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0022) (nb068_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0024) (nb068_wpp_notmem_0025 x y f) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))))

noncomputable def nb068_wpp_refl_0010 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_069), (nb068_alpha_dummy_072 f)), ((nb068_alpha_dummy_068), (nb068_alpha_dummy_071 f)), ((nb068_alpha_dummy_067), (nb068_alpha_dummy_070 f)), ((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)), ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)), ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)), ((nb068_alpha_dummy_087), (nb068_alpha_dummy_088 f)), ((nb068_alpha_dummy_085), (nb068_alpha_dummy_086 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0010 x y f)

theorem nb068_wpp_notmem_0202 : (nb068_alpha_dummy_087) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_087, fv_syn_c0] using (nb068_compact_fv_empty_0064)

theorem nb068_wpp_notmem_0203 (f : Var) : (nb068_alpha_dummy_088 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_088, fv_syn_c0] using (nb068_compact_fv_empty_0065 f)

theorem nb068_wpp_notmem_0204 : (nb068_alpha_dummy_085) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_085, fv_syn_c0] using (nb068_compact_fv_empty_0066)

theorem nb068_wpp_notmem_0205 (f : Var) : (nb068_alpha_dummy_086 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_086, fv_syn_c0] using (nb068_compact_fv_empty_0067 f)

theorem nb068_wpp_notmem_0206 : (nb068_alpha_dummy_083) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_083, fv_syn_c0] using (nb068_compact_fv_empty_0068)

theorem nb068_wpp_notmem_0207 (f : Var) : (nb068_alpha_dummy_084 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_084, fv_syn_c0] using (nb068_compact_fv_empty_0069 f)

theorem nb068_compact_envfresh_0011 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_069), (nb068_alpha_dummy_072 f)), ((nb068_alpha_dummy_068), (nb068_alpha_dummy_071 f)), ((nb068_alpha_dummy_067), (nb068_alpha_dummy_070 f)), ((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)), ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)), ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)), ((nb068_alpha_dummy_087), (nb068_alpha_dummy_088 f)), ((nb068_alpha_dummy_085), (nb068_alpha_dummy_086 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_069) (nb068_alpha_dummy_072 f) (nb068_wpp_notmem_0138) (nb068_wpp_notmem_0139 f) (TEnvFresh.consFresh (nb068_alpha_dummy_068) (nb068_alpha_dummy_071 f) (nb068_wpp_notmem_0140) (nb068_wpp_notmem_0141 f) (TEnvFresh.consFresh (nb068_alpha_dummy_067) (nb068_alpha_dummy_070 f) (nb068_wpp_notmem_0142) (nb068_wpp_notmem_0143 f) (TEnvFresh.consFresh (nb068_alpha_dummy_065) (nb068_alpha_dummy_066 f) (nb068_wpp_notmem_0144) (nb068_wpp_notmem_0145 f) (TEnvFresh.consFresh (nb068_alpha_dummy_061) (nb068_alpha_dummy_063 f) (nb068_wpp_notmem_0146) (nb068_wpp_notmem_0147 f) (TEnvFresh.consFresh (nb068_alpha_dummy_062) (nb068_alpha_dummy_064 f) (nb068_wpp_notmem_0148) (nb068_wpp_notmem_0149 f) (TEnvFresh.consFresh (nb068_alpha_dummy_087) (nb068_alpha_dummy_088 f) (nb068_wpp_notmem_0202) (nb068_wpp_notmem_0203 f) (TEnvFresh.consFresh (nb068_alpha_dummy_085) (nb068_alpha_dummy_086 f) (nb068_wpp_notmem_0204) (nb068_wpp_notmem_0205 f) (TEnvFresh.consFresh (nb068_alpha_dummy_054) (nb068_alpha_dummy_056 f) (nb068_wpp_notmem_0150) (nb068_wpp_notmem_0151 f) (TEnvFresh.consFresh (nb068_alpha_dummy_053) (nb068_alpha_dummy_055 f) (nb068_wpp_notmem_0152) (nb068_wpp_notmem_0153 f) (TEnvFresh.consFresh (nb068_alpha_dummy_083) (nb068_alpha_dummy_084 f) (nb068_wpp_notmem_0206) (nb068_wpp_notmem_0207 f) (TEnvFresh.consFresh (nb068_alpha_dummy_057) (nb068_alpha_dummy_058 f) (nb068_wpp_notmem_0156) (nb068_wpp_notmem_0157 f) (TEnvFresh.consFresh (nb068_alpha_dummy_046) (nb068_alpha_dummy_049 f) (nb068_wpp_notmem_0158) (nb068_wpp_notmem_0159 f) (TEnvFresh.consFresh (nb068_alpha_dummy_045) (nb068_alpha_dummy_048 f) (nb068_wpp_notmem_0160) (nb068_wpp_notmem_0161 f) (TEnvFresh.consFresh (nb068_alpha_dummy_051) (nb068_alpha_dummy_052 f) (nb068_wpp_notmem_0162) (nb068_wpp_notmem_0163 f) (TEnvFresh.consFresh (nb068_alpha_dummy_043) (nb068_alpha_dummy_044 f) (nb068_wpp_notmem_0164) (nb068_wpp_notmem_0165 f) (TEnvFresh.consFresh (nb068_alpha_dummy_041) (nb068_alpha_dummy_042 f) (nb068_wpp_notmem_0166) (nb068_wpp_notmem_0167 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0168) (nb068_wpp_notmem_0169 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0046) (nb068_wpp_notmem_0047 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0048) (nb068_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0050) (nb068_wpp_notmem_0051 x y f) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))))

noncomputable def nb068_wpp_refl_0011 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_069), (nb068_alpha_dummy_072 f)), ((nb068_alpha_dummy_068), (nb068_alpha_dummy_071 f)), ((nb068_alpha_dummy_067), (nb068_alpha_dummy_070 f)), ((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)), ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)), ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)), ((nb068_alpha_dummy_087), (nb068_alpha_dummy_088 f)), ((nb068_alpha_dummy_085), (nb068_alpha_dummy_086 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0011 x y f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
