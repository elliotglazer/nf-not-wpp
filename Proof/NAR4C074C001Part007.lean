import NAR4C074C001Part006

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

theorem nb074_wpp_notmem_0137 (x : Var) : (nb074_alpha_dummy_044 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_044, fv_syn_c1c] using (nb074_compact_fv_empty_0033 x)

theorem nb074_wpp_notmem_0138 : (nb074_alpha_dummy_041) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_041, fv_syn_c1c] using (nb074_compact_fv_empty_0034)

theorem nb074_wpp_notmem_0139 (x : Var) : (nb074_alpha_dummy_043 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_043, fv_syn_c1c] using (nb074_compact_fv_empty_0035 x)

theorem nb074_compact_envfresh_0009 (x : Var) : TEnvFresh [((nb074_alpha_dummy_061), (nb074_alpha_dummy_064 x)), ((nb074_alpha_dummy_060), (nb074_alpha_dummy_063 x)), ((nb074_alpha_dummy_059), (nb074_alpha_dummy_062 x)), ((nb074_alpha_dummy_057), (nb074_alpha_dummy_058 x)), ((nb074_alpha_dummy_053), (nb074_alpha_dummy_055 x)), ((nb074_alpha_dummy_054), (nb074_alpha_dummy_056 x)), ((nb074_alpha_dummy_046), (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)), ((nb074_alpha_dummy_051), (nb074_alpha_dummy_052 x)), ((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb074_alpha_dummy_061) (nb074_alpha_dummy_064 x) (nb074_wpp_notmem_0116) (nb074_wpp_notmem_0117 x) (TEnvFresh.consFresh (nb074_alpha_dummy_060) (nb074_alpha_dummy_063 x) (nb074_wpp_notmem_0118) (nb074_wpp_notmem_0119 x) (TEnvFresh.consFresh (nb074_alpha_dummy_059) (nb074_alpha_dummy_062 x) (nb074_wpp_notmem_0120) (nb074_wpp_notmem_0121 x) (TEnvFresh.consFresh (nb074_alpha_dummy_057) (nb074_alpha_dummy_058 x) (nb074_wpp_notmem_0122) (nb074_wpp_notmem_0123 x) (TEnvFresh.consFresh (nb074_alpha_dummy_053) (nb074_alpha_dummy_055 x) (nb074_wpp_notmem_0124) (nb074_wpp_notmem_0125 x) (TEnvFresh.consFresh (nb074_alpha_dummy_054) (nb074_alpha_dummy_056 x) (nb074_wpp_notmem_0126) (nb074_wpp_notmem_0127 x) (TEnvFresh.consFresh (nb074_alpha_dummy_046) (nb074_alpha_dummy_048 x) (nb074_wpp_notmem_0128) (nb074_wpp_notmem_0129 x) (TEnvFresh.consFresh (nb074_alpha_dummy_045) (nb074_alpha_dummy_047 x) (nb074_wpp_notmem_0130) (nb074_wpp_notmem_0131 x) (TEnvFresh.consFresh (nb074_alpha_dummy_051) (nb074_alpha_dummy_052 x) (nb074_wpp_notmem_0132) (nb074_wpp_notmem_0133 x) (TEnvFresh.consFresh (nb074_alpha_dummy_049) (nb074_alpha_dummy_050 x) (nb074_wpp_notmem_0134) (nb074_wpp_notmem_0135 x) (TEnvFresh.consFresh (nb074_alpha_dummy_042) (nb074_alpha_dummy_044 x) (nb074_wpp_notmem_0136) (nb074_wpp_notmem_0137 x) (TEnvFresh.consFresh (nb074_alpha_dummy_041) (nb074_alpha_dummy_043 x) (nb074_wpp_notmem_0138) (nb074_wpp_notmem_0139 x) (TEnvFresh.consFresh (nb074_alpha_dummy_001) (nb074_alpha_dummy_002 x) (nb074_wpp_notmem_0020) (nb074_wpp_notmem_0021 x) (TEnvFresh.consFresh (nb074_alpha_dummy_000) x (nb074_wpp_notmem_0022) (nb074_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb074_alpha_dummy_003) (nb074_alpha_dummy_004 x) (nb074_wpp_notmem_0024) (nb074_wpp_notmem_0025 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb074_wpp_refl_0009 (x : Var) : TReflOn [((nb074_alpha_dummy_061), (nb074_alpha_dummy_064 x)), ((nb074_alpha_dummy_060), (nb074_alpha_dummy_063 x)), ((nb074_alpha_dummy_059), (nb074_alpha_dummy_062 x)), ((nb074_alpha_dummy_057), (nb074_alpha_dummy_058 x)), ((nb074_alpha_dummy_053), (nb074_alpha_dummy_055 x)), ((nb074_alpha_dummy_054), (nb074_alpha_dummy_056 x)), ((nb074_alpha_dummy_046), (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)), ((nb074_alpha_dummy_051), (nb074_alpha_dummy_052 x)), ((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb074_compact_envfresh_0009 x)

theorem nb074_wpp_notmem_0140 : (nb074_alpha_dummy_061) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_061, fv_syn_c0] using (nb074_compact_fv_empty_0036)

theorem nb074_wpp_notmem_0141 (x : Var) : (nb074_alpha_dummy_064 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_064, fv_syn_c0] using (nb074_compact_fv_empty_0037 x)

theorem nb074_wpp_notmem_0142 : (nb074_alpha_dummy_060) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_060, fv_syn_c0] using (nb074_compact_fv_empty_0038)

theorem nb074_wpp_notmem_0143 (x : Var) : (nb074_alpha_dummy_063 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_063, fv_syn_c0] using (nb074_compact_fv_empty_0039 x)

theorem nb074_wpp_notmem_0144 : (nb074_alpha_dummy_059) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_059, fv_syn_c0] using (nb074_compact_fv_empty_0040)

theorem nb074_wpp_notmem_0145 (x : Var) : (nb074_alpha_dummy_062 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_062, fv_syn_c0] using (nb074_compact_fv_empty_0041 x)

theorem nb074_wpp_notmem_0146 : (nb074_alpha_dummy_057) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_057, fv_syn_c0] using (nb074_compact_fv_empty_0042)

theorem nb074_wpp_notmem_0147 (x : Var) : (nb074_alpha_dummy_058 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_058, fv_syn_c0] using (nb074_compact_fv_empty_0043 x)

theorem nb074_wpp_notmem_0148 : (nb074_alpha_dummy_053) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_053, fv_syn_c0] using (nb074_compact_fv_empty_0044)

theorem nb074_wpp_notmem_0149 (x : Var) : (nb074_alpha_dummy_055 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_055, fv_syn_c0] using (nb074_compact_fv_empty_0045 x)

theorem nb074_wpp_notmem_0150 : (nb074_alpha_dummy_054) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_054, fv_syn_c0] using (nb074_compact_fv_empty_0046)

theorem nb074_wpp_notmem_0151 (x : Var) : (nb074_alpha_dummy_056 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_056, fv_syn_c0] using (nb074_compact_fv_empty_0047 x)

theorem nb074_wpp_notmem_0152 : (nb074_alpha_dummy_046) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_046, fv_syn_c0] using (nb074_compact_fv_empty_0048)

theorem nb074_wpp_notmem_0153 (x : Var) : (nb074_alpha_dummy_048 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_048, fv_syn_c0] using (nb074_compact_fv_empty_0049 x)

theorem nb074_wpp_notmem_0154 : (nb074_alpha_dummy_045) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_045, fv_syn_c0] using (nb074_compact_fv_empty_0050)

theorem nb074_wpp_notmem_0155 (x : Var) : (nb074_alpha_dummy_047 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_047, fv_syn_c0] using (nb074_compact_fv_empty_0051 x)

theorem nb074_wpp_notmem_0156 : (nb074_alpha_dummy_051) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_051, fv_syn_c0] using (nb074_compact_fv_empty_0052)

theorem nb074_wpp_notmem_0157 (x : Var) : (nb074_alpha_dummy_052 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_052, fv_syn_c0] using (nb074_compact_fv_empty_0053 x)

theorem nb074_wpp_notmem_0158 : (nb074_alpha_dummy_049) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_049, fv_syn_c0] using (nb074_compact_fv_empty_0054)

theorem nb074_wpp_notmem_0159 (x : Var) : (nb074_alpha_dummy_050 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_050, fv_syn_c0] using (nb074_compact_fv_empty_0055 x)

theorem nb074_wpp_notmem_0160 : (nb074_alpha_dummy_042) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_042, fv_syn_c0] using (nb074_compact_fv_empty_0032)

theorem nb074_wpp_notmem_0161 (x : Var) : (nb074_alpha_dummy_044 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_044, fv_syn_c0] using (nb074_compact_fv_empty_0033 x)

theorem nb074_wpp_notmem_0162 : (nb074_alpha_dummy_041) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_041, fv_syn_c0] using (nb074_compact_fv_empty_0034)

theorem nb074_wpp_notmem_0163 (x : Var) : (nb074_alpha_dummy_043 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_043, fv_syn_c0] using (nb074_compact_fv_empty_0035 x)

theorem nb074_compact_envfresh_0010 (x : Var) : TEnvFresh [((nb074_alpha_dummy_061), (nb074_alpha_dummy_064 x)), ((nb074_alpha_dummy_060), (nb074_alpha_dummy_063 x)), ((nb074_alpha_dummy_059), (nb074_alpha_dummy_062 x)), ((nb074_alpha_dummy_057), (nb074_alpha_dummy_058 x)), ((nb074_alpha_dummy_053), (nb074_alpha_dummy_055 x)), ((nb074_alpha_dummy_054), (nb074_alpha_dummy_056 x)), ((nb074_alpha_dummy_046), (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)), ((nb074_alpha_dummy_051), (nb074_alpha_dummy_052 x)), ((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb074_alpha_dummy_061) (nb074_alpha_dummy_064 x) (nb074_wpp_notmem_0140) (nb074_wpp_notmem_0141 x) (TEnvFresh.consFresh (nb074_alpha_dummy_060) (nb074_alpha_dummy_063 x) (nb074_wpp_notmem_0142) (nb074_wpp_notmem_0143 x) (TEnvFresh.consFresh (nb074_alpha_dummy_059) (nb074_alpha_dummy_062 x) (nb074_wpp_notmem_0144) (nb074_wpp_notmem_0145 x) (TEnvFresh.consFresh (nb074_alpha_dummy_057) (nb074_alpha_dummy_058 x) (nb074_wpp_notmem_0146) (nb074_wpp_notmem_0147 x) (TEnvFresh.consFresh (nb074_alpha_dummy_053) (nb074_alpha_dummy_055 x) (nb074_wpp_notmem_0148) (nb074_wpp_notmem_0149 x) (TEnvFresh.consFresh (nb074_alpha_dummy_054) (nb074_alpha_dummy_056 x) (nb074_wpp_notmem_0150) (nb074_wpp_notmem_0151 x) (TEnvFresh.consFresh (nb074_alpha_dummy_046) (nb074_alpha_dummy_048 x) (nb074_wpp_notmem_0152) (nb074_wpp_notmem_0153 x) (TEnvFresh.consFresh (nb074_alpha_dummy_045) (nb074_alpha_dummy_047 x) (nb074_wpp_notmem_0154) (nb074_wpp_notmem_0155 x) (TEnvFresh.consFresh (nb074_alpha_dummy_051) (nb074_alpha_dummy_052 x) (nb074_wpp_notmem_0156) (nb074_wpp_notmem_0157 x) (TEnvFresh.consFresh (nb074_alpha_dummy_049) (nb074_alpha_dummy_050 x) (nb074_wpp_notmem_0158) (nb074_wpp_notmem_0159 x) (TEnvFresh.consFresh (nb074_alpha_dummy_042) (nb074_alpha_dummy_044 x) (nb074_wpp_notmem_0160) (nb074_wpp_notmem_0161 x) (TEnvFresh.consFresh (nb074_alpha_dummy_041) (nb074_alpha_dummy_043 x) (nb074_wpp_notmem_0162) (nb074_wpp_notmem_0163 x) (TEnvFresh.consFresh (nb074_alpha_dummy_001) (nb074_alpha_dummy_002 x) (nb074_wpp_notmem_0046) (nb074_wpp_notmem_0047 x) (TEnvFresh.consFresh (nb074_alpha_dummy_000) x (nb074_wpp_notmem_0048) (nb074_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb074_alpha_dummy_003) (nb074_alpha_dummy_004 x) (nb074_wpp_notmem_0050) (nb074_wpp_notmem_0051 x) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))

noncomputable def nb074_wpp_refl_0010 (x : Var) : TReflOn [((nb074_alpha_dummy_061), (nb074_alpha_dummy_064 x)), ((nb074_alpha_dummy_060), (nb074_alpha_dummy_063 x)), ((nb074_alpha_dummy_059), (nb074_alpha_dummy_062 x)), ((nb074_alpha_dummy_057), (nb074_alpha_dummy_058 x)), ((nb074_alpha_dummy_053), (nb074_alpha_dummy_055 x)), ((nb074_alpha_dummy_054), (nb074_alpha_dummy_056 x)), ((nb074_alpha_dummy_046), (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)), ((nb074_alpha_dummy_051), (nb074_alpha_dummy_052 x)), ((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb074_compact_envfresh_0010 x)

theorem nb074_wpp_notmem_0164 : (nb074_alpha_dummy_057) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_057, fv_syn_cnnc] using (nb074_compact_fv_empty_0042)

theorem nb074_wpp_notmem_0165 (x : Var) : (nb074_alpha_dummy_058 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_058, fv_syn_cnnc] using (nb074_compact_fv_empty_0043 x)

theorem nb074_wpp_notmem_0166 : (nb074_alpha_dummy_053) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_053, fv_syn_cnnc] using (nb074_compact_fv_empty_0044)

theorem nb074_wpp_notmem_0167 (x : Var) : (nb074_alpha_dummy_055 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_055, fv_syn_cnnc] using (nb074_compact_fv_empty_0045 x)

theorem nb074_wpp_notmem_0168 : (nb074_alpha_dummy_054) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_054, fv_syn_cnnc] using (nb074_compact_fv_empty_0046)

theorem nb074_wpp_notmem_0169 (x : Var) : (nb074_alpha_dummy_056 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_056, fv_syn_cnnc] using (nb074_compact_fv_empty_0047 x)

theorem nb074_wpp_notmem_0170 : (nb074_alpha_dummy_046) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_046, fv_syn_cnnc] using (nb074_compact_fv_empty_0048)

theorem nb074_wpp_notmem_0171 (x : Var) : (nb074_alpha_dummy_048 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_048, fv_syn_cnnc] using (nb074_compact_fv_empty_0049 x)

theorem nb074_wpp_notmem_0172 : (nb074_alpha_dummy_045) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_045, fv_syn_cnnc] using (nb074_compact_fv_empty_0050)

theorem nb074_wpp_notmem_0173 (x : Var) : (nb074_alpha_dummy_047 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_047, fv_syn_cnnc] using (nb074_compact_fv_empty_0051 x)

theorem nb074_wpp_notmem_0174 : (nb074_alpha_dummy_051) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_051, fv_syn_cnnc] using (nb074_compact_fv_empty_0052)

theorem nb074_wpp_notmem_0175 (x : Var) : (nb074_alpha_dummy_052 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_052, fv_syn_cnnc] using (nb074_compact_fv_empty_0053 x)

theorem nb074_wpp_notmem_0176 : (nb074_alpha_dummy_049) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_049, fv_syn_cnnc] using (nb074_compact_fv_empty_0054)

theorem nb074_wpp_notmem_0177 (x : Var) : (nb074_alpha_dummy_050 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_050, fv_syn_cnnc] using (nb074_compact_fv_empty_0055 x)

theorem nb074_wpp_notmem_0178 : (nb074_alpha_dummy_042) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_042, fv_syn_cnnc] using (nb074_compact_fv_empty_0032)

theorem nb074_wpp_notmem_0179 (x : Var) : (nb074_alpha_dummy_044 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_044, fv_syn_cnnc] using (nb074_compact_fv_empty_0033 x)

theorem nb074_wpp_notmem_0180 : (nb074_alpha_dummy_041) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_041, fv_syn_cnnc] using (nb074_compact_fv_empty_0034)

theorem nb074_wpp_notmem_0181 (x : Var) : (nb074_alpha_dummy_043 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_043, fv_syn_cnnc] using (nb074_compact_fv_empty_0035 x)

theorem nb074_compact_envfresh_0011 (x : Var) : TEnvFresh [((nb074_alpha_dummy_057), (nb074_alpha_dummy_058 x)), ((nb074_alpha_dummy_053), (nb074_alpha_dummy_055 x)), ((nb074_alpha_dummy_054), (nb074_alpha_dummy_056 x)), ((nb074_alpha_dummy_046), (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)), ((nb074_alpha_dummy_051), (nb074_alpha_dummy_052 x)), ((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb074_alpha_dummy_057) (nb074_alpha_dummy_058 x) (nb074_wpp_notmem_0164) (nb074_wpp_notmem_0165 x) (TEnvFresh.consFresh (nb074_alpha_dummy_053) (nb074_alpha_dummy_055 x) (nb074_wpp_notmem_0166) (nb074_wpp_notmem_0167 x) (TEnvFresh.consFresh (nb074_alpha_dummy_054) (nb074_alpha_dummy_056 x) (nb074_wpp_notmem_0168) (nb074_wpp_notmem_0169 x) (TEnvFresh.consFresh (nb074_alpha_dummy_046) (nb074_alpha_dummy_048 x) (nb074_wpp_notmem_0170) (nb074_wpp_notmem_0171 x) (TEnvFresh.consFresh (nb074_alpha_dummy_045) (nb074_alpha_dummy_047 x) (nb074_wpp_notmem_0172) (nb074_wpp_notmem_0173 x) (TEnvFresh.consFresh (nb074_alpha_dummy_051) (nb074_alpha_dummy_052 x) (nb074_wpp_notmem_0174) (nb074_wpp_notmem_0175 x) (TEnvFresh.consFresh (nb074_alpha_dummy_049) (nb074_alpha_dummy_050 x) (nb074_wpp_notmem_0176) (nb074_wpp_notmem_0177 x) (TEnvFresh.consFresh (nb074_alpha_dummy_042) (nb074_alpha_dummy_044 x) (nb074_wpp_notmem_0178) (nb074_wpp_notmem_0179 x) (TEnvFresh.consFresh (nb074_alpha_dummy_041) (nb074_alpha_dummy_043 x) (nb074_wpp_notmem_0180) (nb074_wpp_notmem_0181 x) (TEnvFresh.consFresh (nb074_alpha_dummy_001) (nb074_alpha_dummy_002 x) (nb074_wpp_notmem_0066) (nb074_wpp_notmem_0067 x) (TEnvFresh.consFresh (nb074_alpha_dummy_000) x (nb074_wpp_notmem_0068) (nb074_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb074_alpha_dummy_003) (nb074_alpha_dummy_004 x) (nb074_wpp_notmem_0070) (nb074_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))

noncomputable def nb074_wpp_refl_0011 (x : Var) : TReflOn [((nb074_alpha_dummy_057), (nb074_alpha_dummy_058 x)), ((nb074_alpha_dummy_053), (nb074_alpha_dummy_055 x)), ((nb074_alpha_dummy_054), (nb074_alpha_dummy_056 x)), ((nb074_alpha_dummy_046), (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)), ((nb074_alpha_dummy_051), (nb074_alpha_dummy_052 x)), ((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb074_compact_envfresh_0011 x)

theorem nb074_compact_fv_empty_0056 : (nb074_alpha_dummy_079) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0182 : (nb074_alpha_dummy_079) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_079, fv_syn_c1c] using (nb074_compact_fv_empty_0056)

theorem nb074_compact_fv_empty_0057 (x : Var) : (nb074_alpha_dummy_080 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0183 (x : Var) : (nb074_alpha_dummy_080 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_080, fv_syn_c1c] using (nb074_compact_fv_empty_0057 x)

theorem nb074_compact_fv_empty_0058 : (nb074_alpha_dummy_077) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0184 : (nb074_alpha_dummy_077) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_077, fv_syn_c1c] using (nb074_compact_fv_empty_0058)

theorem nb074_compact_fv_empty_0059 (x : Var) : (nb074_alpha_dummy_078 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0185 (x : Var) : (nb074_alpha_dummy_078 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_078, fv_syn_c1c] using (nb074_compact_fv_empty_0059 x)

theorem nb074_compact_fv_empty_0060 : (nb074_alpha_dummy_075) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0186 : (nb074_alpha_dummy_075) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_075, fv_syn_c1c] using (nb074_compact_fv_empty_0060)

theorem nb074_compact_fv_empty_0061 (x : Var) : (nb074_alpha_dummy_076 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0187 (x : Var) : (nb074_alpha_dummy_076 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_076, fv_syn_c1c] using (nb074_compact_fv_empty_0061 x)

theorem nb074_compact_envfresh_0012 (x : Var) : TEnvFresh [((nb074_alpha_dummy_061), (nb074_alpha_dummy_064 x)), ((nb074_alpha_dummy_060), (nb074_alpha_dummy_063 x)), ((nb074_alpha_dummy_059), (nb074_alpha_dummy_062 x)), ((nb074_alpha_dummy_057), (nb074_alpha_dummy_058 x)), ((nb074_alpha_dummy_053), (nb074_alpha_dummy_055 x)), ((nb074_alpha_dummy_054), (nb074_alpha_dummy_056 x)), ((nb074_alpha_dummy_079), (nb074_alpha_dummy_080 x)), ((nb074_alpha_dummy_077), (nb074_alpha_dummy_078 x)), ((nb074_alpha_dummy_046), (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)), ((nb074_alpha_dummy_075), (nb074_alpha_dummy_076 x)), ((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb074_alpha_dummy_061) (nb074_alpha_dummy_064 x) (nb074_wpp_notmem_0116) (nb074_wpp_notmem_0117 x) (TEnvFresh.consFresh (nb074_alpha_dummy_060) (nb074_alpha_dummy_063 x) (nb074_wpp_notmem_0118) (nb074_wpp_notmem_0119 x) (TEnvFresh.consFresh (nb074_alpha_dummy_059) (nb074_alpha_dummy_062 x) (nb074_wpp_notmem_0120) (nb074_wpp_notmem_0121 x) (TEnvFresh.consFresh (nb074_alpha_dummy_057) (nb074_alpha_dummy_058 x) (nb074_wpp_notmem_0122) (nb074_wpp_notmem_0123 x) (TEnvFresh.consFresh (nb074_alpha_dummy_053) (nb074_alpha_dummy_055 x) (nb074_wpp_notmem_0124) (nb074_wpp_notmem_0125 x) (TEnvFresh.consFresh (nb074_alpha_dummy_054) (nb074_alpha_dummy_056 x) (nb074_wpp_notmem_0126) (nb074_wpp_notmem_0127 x) (TEnvFresh.consFresh (nb074_alpha_dummy_079) (nb074_alpha_dummy_080 x) (nb074_wpp_notmem_0182) (nb074_wpp_notmem_0183 x) (TEnvFresh.consFresh (nb074_alpha_dummy_077) (nb074_alpha_dummy_078 x) (nb074_wpp_notmem_0184) (nb074_wpp_notmem_0185 x) (TEnvFresh.consFresh (nb074_alpha_dummy_046) (nb074_alpha_dummy_048 x) (nb074_wpp_notmem_0128) (nb074_wpp_notmem_0129 x) (TEnvFresh.consFresh (nb074_alpha_dummy_045) (nb074_alpha_dummy_047 x) (nb074_wpp_notmem_0130) (nb074_wpp_notmem_0131 x) (TEnvFresh.consFresh (nb074_alpha_dummy_075) (nb074_alpha_dummy_076 x) (nb074_wpp_notmem_0186) (nb074_wpp_notmem_0187 x) (TEnvFresh.consFresh (nb074_alpha_dummy_049) (nb074_alpha_dummy_050 x) (nb074_wpp_notmem_0134) (nb074_wpp_notmem_0135 x) (TEnvFresh.consFresh (nb074_alpha_dummy_042) (nb074_alpha_dummy_044 x) (nb074_wpp_notmem_0136) (nb074_wpp_notmem_0137 x) (TEnvFresh.consFresh (nb074_alpha_dummy_041) (nb074_alpha_dummy_043 x) (nb074_wpp_notmem_0138) (nb074_wpp_notmem_0139 x) (TEnvFresh.consFresh (nb074_alpha_dummy_001) (nb074_alpha_dummy_002 x) (nb074_wpp_notmem_0020) (nb074_wpp_notmem_0021 x) (TEnvFresh.consFresh (nb074_alpha_dummy_000) x (nb074_wpp_notmem_0022) (nb074_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb074_alpha_dummy_003) (nb074_alpha_dummy_004 x) (nb074_wpp_notmem_0024) (nb074_wpp_notmem_0025 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))

noncomputable def nb074_wpp_refl_0012 (x : Var) : TReflOn [((nb074_alpha_dummy_061), (nb074_alpha_dummy_064 x)), ((nb074_alpha_dummy_060), (nb074_alpha_dummy_063 x)), ((nb074_alpha_dummy_059), (nb074_alpha_dummy_062 x)), ((nb074_alpha_dummy_057), (nb074_alpha_dummy_058 x)), ((nb074_alpha_dummy_053), (nb074_alpha_dummy_055 x)), ((nb074_alpha_dummy_054), (nb074_alpha_dummy_056 x)), ((nb074_alpha_dummy_079), (nb074_alpha_dummy_080 x)), ((nb074_alpha_dummy_077), (nb074_alpha_dummy_078 x)), ((nb074_alpha_dummy_046), (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)), ((nb074_alpha_dummy_075), (nb074_alpha_dummy_076 x)), ((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb074_compact_envfresh_0012 x)

theorem nb074_wpp_notmem_0188 : (nb074_alpha_dummy_079) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_079, fv_syn_c0] using (nb074_compact_fv_empty_0056)

theorem nb074_wpp_notmem_0189 (x : Var) : (nb074_alpha_dummy_080 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_080, fv_syn_c0] using (nb074_compact_fv_empty_0057 x)

theorem nb074_wpp_notmem_0190 : (nb074_alpha_dummy_077) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_077, fv_syn_c0] using (nb074_compact_fv_empty_0058)

theorem nb074_wpp_notmem_0191 (x : Var) : (nb074_alpha_dummy_078 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_078, fv_syn_c0] using (nb074_compact_fv_empty_0059 x)

theorem nb074_wpp_notmem_0192 : (nb074_alpha_dummy_075) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_075, fv_syn_c0] using (nb074_compact_fv_empty_0060)

theorem nb074_wpp_notmem_0193 (x : Var) : (nb074_alpha_dummy_076 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_076, fv_syn_c0] using (nb074_compact_fv_empty_0061 x)

theorem nb074_compact_envfresh_0013 (x : Var) : TEnvFresh [((nb074_alpha_dummy_061), (nb074_alpha_dummy_064 x)), ((nb074_alpha_dummy_060), (nb074_alpha_dummy_063 x)), ((nb074_alpha_dummy_059), (nb074_alpha_dummy_062 x)), ((nb074_alpha_dummy_057), (nb074_alpha_dummy_058 x)), ((nb074_alpha_dummy_053), (nb074_alpha_dummy_055 x)), ((nb074_alpha_dummy_054), (nb074_alpha_dummy_056 x)), ((nb074_alpha_dummy_079), (nb074_alpha_dummy_080 x)), ((nb074_alpha_dummy_077), (nb074_alpha_dummy_078 x)), ((nb074_alpha_dummy_046), (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)), ((nb074_alpha_dummy_075), (nb074_alpha_dummy_076 x)), ((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb074_alpha_dummy_061) (nb074_alpha_dummy_064 x) (nb074_wpp_notmem_0140) (nb074_wpp_notmem_0141 x) (TEnvFresh.consFresh (nb074_alpha_dummy_060) (nb074_alpha_dummy_063 x) (nb074_wpp_notmem_0142) (nb074_wpp_notmem_0143 x) (TEnvFresh.consFresh (nb074_alpha_dummy_059) (nb074_alpha_dummy_062 x) (nb074_wpp_notmem_0144) (nb074_wpp_notmem_0145 x) (TEnvFresh.consFresh (nb074_alpha_dummy_057) (nb074_alpha_dummy_058 x) (nb074_wpp_notmem_0146) (nb074_wpp_notmem_0147 x) (TEnvFresh.consFresh (nb074_alpha_dummy_053) (nb074_alpha_dummy_055 x) (nb074_wpp_notmem_0148) (nb074_wpp_notmem_0149 x) (TEnvFresh.consFresh (nb074_alpha_dummy_054) (nb074_alpha_dummy_056 x) (nb074_wpp_notmem_0150) (nb074_wpp_notmem_0151 x) (TEnvFresh.consFresh (nb074_alpha_dummy_079) (nb074_alpha_dummy_080 x) (nb074_wpp_notmem_0188) (nb074_wpp_notmem_0189 x) (TEnvFresh.consFresh (nb074_alpha_dummy_077) (nb074_alpha_dummy_078 x) (nb074_wpp_notmem_0190) (nb074_wpp_notmem_0191 x) (TEnvFresh.consFresh (nb074_alpha_dummy_046) (nb074_alpha_dummy_048 x) (nb074_wpp_notmem_0152) (nb074_wpp_notmem_0153 x) (TEnvFresh.consFresh (nb074_alpha_dummy_045) (nb074_alpha_dummy_047 x) (nb074_wpp_notmem_0154) (nb074_wpp_notmem_0155 x) (TEnvFresh.consFresh (nb074_alpha_dummy_075) (nb074_alpha_dummy_076 x) (nb074_wpp_notmem_0192) (nb074_wpp_notmem_0193 x) (TEnvFresh.consFresh (nb074_alpha_dummy_049) (nb074_alpha_dummy_050 x) (nb074_wpp_notmem_0158) (nb074_wpp_notmem_0159 x) (TEnvFresh.consFresh (nb074_alpha_dummy_042) (nb074_alpha_dummy_044 x) (nb074_wpp_notmem_0160) (nb074_wpp_notmem_0161 x) (TEnvFresh.consFresh (nb074_alpha_dummy_041) (nb074_alpha_dummy_043 x) (nb074_wpp_notmem_0162) (nb074_wpp_notmem_0163 x) (TEnvFresh.consFresh (nb074_alpha_dummy_001) (nb074_alpha_dummy_002 x) (nb074_wpp_notmem_0046) (nb074_wpp_notmem_0047 x) (TEnvFresh.consFresh (nb074_alpha_dummy_000) x (nb074_wpp_notmem_0048) (nb074_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb074_alpha_dummy_003) (nb074_alpha_dummy_004 x) (nb074_wpp_notmem_0050) (nb074_wpp_notmem_0051 x) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))

noncomputable def nb074_wpp_refl_0013 (x : Var) : TReflOn [((nb074_alpha_dummy_061), (nb074_alpha_dummy_064 x)), ((nb074_alpha_dummy_060), (nb074_alpha_dummy_063 x)), ((nb074_alpha_dummy_059), (nb074_alpha_dummy_062 x)), ((nb074_alpha_dummy_057), (nb074_alpha_dummy_058 x)), ((nb074_alpha_dummy_053), (nb074_alpha_dummy_055 x)), ((nb074_alpha_dummy_054), (nb074_alpha_dummy_056 x)), ((nb074_alpha_dummy_079), (nb074_alpha_dummy_080 x)), ((nb074_alpha_dummy_077), (nb074_alpha_dummy_078 x)), ((nb074_alpha_dummy_046), (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)), ((nb074_alpha_dummy_075), (nb074_alpha_dummy_076 x)), ((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb074_compact_envfresh_0013 x)

theorem nb074_wpp_notmem_0194 : (nb074_alpha_dummy_079) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_079, fv_syn_cnnc] using (nb074_compact_fv_empty_0056)

theorem nb074_wpp_notmem_0195 (x : Var) : (nb074_alpha_dummy_080 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_080, fv_syn_cnnc] using (nb074_compact_fv_empty_0057 x)

theorem nb074_wpp_notmem_0196 : (nb074_alpha_dummy_077) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_077, fv_syn_cnnc] using (nb074_compact_fv_empty_0058)

theorem nb074_wpp_notmem_0197 (x : Var) : (nb074_alpha_dummy_078 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_078, fv_syn_cnnc] using (nb074_compact_fv_empty_0059 x)

theorem nb074_wpp_notmem_0198 : (nb074_alpha_dummy_075) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_075, fv_syn_cnnc] using (nb074_compact_fv_empty_0060)

theorem nb074_wpp_notmem_0199 (x : Var) : (nb074_alpha_dummy_076 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb074_alpha_dummy_076, fv_syn_cnnc] using (nb074_compact_fv_empty_0061 x)

theorem nb074_compact_envfresh_0014 (x : Var) : TEnvFresh [((nb074_alpha_dummy_057), (nb074_alpha_dummy_058 x)), ((nb074_alpha_dummy_053), (nb074_alpha_dummy_055 x)), ((nb074_alpha_dummy_054), (nb074_alpha_dummy_056 x)), ((nb074_alpha_dummy_079), (nb074_alpha_dummy_080 x)), ((nb074_alpha_dummy_077), (nb074_alpha_dummy_078 x)), ((nb074_alpha_dummy_046), (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)), ((nb074_alpha_dummy_075), (nb074_alpha_dummy_076 x)), ((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb074_alpha_dummy_057) (nb074_alpha_dummy_058 x) (nb074_wpp_notmem_0164) (nb074_wpp_notmem_0165 x) (TEnvFresh.consFresh (nb074_alpha_dummy_053) (nb074_alpha_dummy_055 x) (nb074_wpp_notmem_0166) (nb074_wpp_notmem_0167 x) (TEnvFresh.consFresh (nb074_alpha_dummy_054) (nb074_alpha_dummy_056 x) (nb074_wpp_notmem_0168) (nb074_wpp_notmem_0169 x) (TEnvFresh.consFresh (nb074_alpha_dummy_079) (nb074_alpha_dummy_080 x) (nb074_wpp_notmem_0194) (nb074_wpp_notmem_0195 x) (TEnvFresh.consFresh (nb074_alpha_dummy_077) (nb074_alpha_dummy_078 x) (nb074_wpp_notmem_0196) (nb074_wpp_notmem_0197 x) (TEnvFresh.consFresh (nb074_alpha_dummy_046) (nb074_alpha_dummy_048 x) (nb074_wpp_notmem_0170) (nb074_wpp_notmem_0171 x) (TEnvFresh.consFresh (nb074_alpha_dummy_045) (nb074_alpha_dummy_047 x) (nb074_wpp_notmem_0172) (nb074_wpp_notmem_0173 x) (TEnvFresh.consFresh (nb074_alpha_dummy_075) (nb074_alpha_dummy_076 x) (nb074_wpp_notmem_0198) (nb074_wpp_notmem_0199 x) (TEnvFresh.consFresh (nb074_alpha_dummy_049) (nb074_alpha_dummy_050 x) (nb074_wpp_notmem_0176) (nb074_wpp_notmem_0177 x) (TEnvFresh.consFresh (nb074_alpha_dummy_042) (nb074_alpha_dummy_044 x) (nb074_wpp_notmem_0178) (nb074_wpp_notmem_0179 x) (TEnvFresh.consFresh (nb074_alpha_dummy_041) (nb074_alpha_dummy_043 x) (nb074_wpp_notmem_0180) (nb074_wpp_notmem_0181 x) (TEnvFresh.consFresh (nb074_alpha_dummy_001) (nb074_alpha_dummy_002 x) (nb074_wpp_notmem_0066) (nb074_wpp_notmem_0067 x) (TEnvFresh.consFresh (nb074_alpha_dummy_000) x (nb074_wpp_notmem_0068) (nb074_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb074_alpha_dummy_003) (nb074_alpha_dummy_004 x) (nb074_wpp_notmem_0070) (nb074_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))

noncomputable def nb074_wpp_refl_0014 (x : Var) : TReflOn [((nb074_alpha_dummy_057), (nb074_alpha_dummy_058 x)), ((nb074_alpha_dummy_053), (nb074_alpha_dummy_055 x)), ((nb074_alpha_dummy_054), (nb074_alpha_dummy_056 x)), ((nb074_alpha_dummy_079), (nb074_alpha_dummy_080 x)), ((nb074_alpha_dummy_077), (nb074_alpha_dummy_078 x)), ((nb074_alpha_dummy_046), (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)), ((nb074_alpha_dummy_075), (nb074_alpha_dummy_076 x)), ((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb074_compact_envfresh_0014 x)

theorem nb074_wpp_notmem_0200 : (nb074_alpha_dummy_077) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_077, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0058)

theorem nb074_wpp_notmem_0201 (x : Var) : (nb074_alpha_dummy_078 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_078, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0059 x)

theorem nb074_wpp_notmem_0202 : (nb074_alpha_dummy_046) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_046, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0048)

theorem nb074_wpp_notmem_0203 (x : Var) : (nb074_alpha_dummy_048 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_048, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0049 x)

theorem nb074_wpp_notmem_0204 : (nb074_alpha_dummy_045) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_045, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0050)

theorem nb074_wpp_notmem_0205 (x : Var) : (nb074_alpha_dummy_047 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_047, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0051 x)

theorem nb074_wpp_notmem_0206 : (nb074_alpha_dummy_075) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_075, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0060)

theorem nb074_wpp_notmem_0207 (x : Var) : (nb074_alpha_dummy_076 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_076, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0061 x)

theorem nb074_wpp_notmem_0208 : (nb074_alpha_dummy_049) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_049, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0054)

theorem nb074_wpp_notmem_0209 (x : Var) : (nb074_alpha_dummy_050 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_050, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0055 x)

theorem nb074_wpp_notmem_0210 : (nb074_alpha_dummy_042) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_042, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0032)

theorem nb074_wpp_notmem_0211 (x : Var) : (nb074_alpha_dummy_044 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_044, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0033 x)

theorem nb074_wpp_notmem_0212 : (nb074_alpha_dummy_041) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_041, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0034)

theorem nb074_wpp_notmem_0213 (x : Var) : (nb074_alpha_dummy_043 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb074_alpha_dummy_043, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb074_compact_fv_empty_0035 x)

theorem nb074_compact_envfresh_0015 (x : Var) : TEnvFresh [((nb074_alpha_dummy_077), (nb074_alpha_dummy_078 x)), ((nb074_alpha_dummy_046), (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)), ((nb074_alpha_dummy_075), (nb074_alpha_dummy_076 x)), ((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb074_alpha_dummy_077) (nb074_alpha_dummy_078 x) (nb074_wpp_notmem_0200) (nb074_wpp_notmem_0201 x) (TEnvFresh.consFresh (nb074_alpha_dummy_046) (nb074_alpha_dummy_048 x) (nb074_wpp_notmem_0202) (nb074_wpp_notmem_0203 x) (TEnvFresh.consFresh (nb074_alpha_dummy_045) (nb074_alpha_dummy_047 x) (nb074_wpp_notmem_0204) (nb074_wpp_notmem_0205 x) (TEnvFresh.consFresh (nb074_alpha_dummy_075) (nb074_alpha_dummy_076 x) (nb074_wpp_notmem_0206) (nb074_wpp_notmem_0207 x) (TEnvFresh.consFresh (nb074_alpha_dummy_049) (nb074_alpha_dummy_050 x) (nb074_wpp_notmem_0208) (nb074_wpp_notmem_0209 x) (TEnvFresh.consFresh (nb074_alpha_dummy_042) (nb074_alpha_dummy_044 x) (nb074_wpp_notmem_0210) (nb074_wpp_notmem_0211 x) (TEnvFresh.consFresh (nb074_alpha_dummy_041) (nb074_alpha_dummy_043 x) (nb074_wpp_notmem_0212) (nb074_wpp_notmem_0213 x) (TEnvFresh.consFresh (nb074_alpha_dummy_001) (nb074_alpha_dummy_002 x) (nb074_wpp_notmem_0100) (nb074_wpp_notmem_0101 x) (TEnvFresh.consFresh (nb074_alpha_dummy_000) x (nb074_wpp_notmem_0102) (nb074_wpp_notmem_0103 x) (TEnvFresh.consFresh (nb074_alpha_dummy_003) (nb074_alpha_dummy_004 x) (nb074_wpp_notmem_0104) (nb074_wpp_notmem_0105 x) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))

noncomputable def nb074_wpp_refl_0015 (x : Var) : TReflOn [((nb074_alpha_dummy_077), (nb074_alpha_dummy_078 x)), ((nb074_alpha_dummy_046), (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)), ((nb074_alpha_dummy_075), (nb074_alpha_dummy_076 x)), ((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb074_compact_envfresh_0015 x)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
