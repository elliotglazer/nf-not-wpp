import NAR4C090C001Part025

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

theorem nb090_compact_envfresh_0011 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_073 A), (nb090_alpha_dummy_076 h)), ((nb090_alpha_dummy_072 A), (nb090_alpha_dummy_075 h)), ((nb090_alpha_dummy_071 A), (nb090_alpha_dummy_074 h)), ((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)), ((nb090_alpha_dummy_065 A), (nb090_alpha_dummy_067 h)), ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)), ((nb090_alpha_dummy_091 A), (nb090_alpha_dummy_092 h)), ((nb090_alpha_dummy_089 A), (nb090_alpha_dummy_090 h)), ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)), ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_087 A), (nb090_alpha_dummy_088 h)), ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_073 A) (nb090_alpha_dummy_076 h) (nb090_wpp_notmem_0112 A) (nb090_wpp_notmem_0113 h) (TEnvFresh.consFresh (nb090_alpha_dummy_072 A) (nb090_alpha_dummy_075 h) (nb090_wpp_notmem_0114 A) (nb090_wpp_notmem_0115 h) (TEnvFresh.consFresh (nb090_alpha_dummy_071 A) (nb090_alpha_dummy_074 h) (nb090_wpp_notmem_0116 A) (nb090_wpp_notmem_0117 h) (TEnvFresh.consFresh (nb090_alpha_dummy_069 A) (nb090_alpha_dummy_070 h) (nb090_wpp_notmem_0118 A) (nb090_wpp_notmem_0119 h) (TEnvFresh.consFresh (nb090_alpha_dummy_065 A) (nb090_alpha_dummy_067 h) (nb090_wpp_notmem_0120 A) (nb090_wpp_notmem_0121 h) (TEnvFresh.consFresh (nb090_alpha_dummy_066 A) (nb090_alpha_dummy_068 h) (nb090_wpp_notmem_0122 A) (nb090_wpp_notmem_0123 h) (TEnvFresh.consFresh (nb090_alpha_dummy_091 A) (nb090_alpha_dummy_092 h) (nb090_wpp_notmem_0202 A) (nb090_wpp_notmem_0203 h) (TEnvFresh.consFresh (nb090_alpha_dummy_089 A) (nb090_alpha_dummy_090 h) (nb090_wpp_notmem_0204 A) (nb090_wpp_notmem_0205 h) (TEnvFresh.consFresh (nb090_alpha_dummy_058 A) (nb090_alpha_dummy_060 h) (nb090_wpp_notmem_0124 A) (nb090_wpp_notmem_0125 h) (TEnvFresh.consFresh (nb090_alpha_dummy_057 A) (nb090_alpha_dummy_059 h) (nb090_wpp_notmem_0126 A) (nb090_wpp_notmem_0127 h) (TEnvFresh.consFresh (nb090_alpha_dummy_087 A) (nb090_alpha_dummy_088 h) (nb090_wpp_notmem_0206 A) (nb090_wpp_notmem_0207 h) (TEnvFresh.consFresh (nb090_alpha_dummy_061 A) (nb090_alpha_dummy_062 h) (nb090_wpp_notmem_0130 A) (nb090_wpp_notmem_0131 h) (TEnvFresh.consFresh (nb090_alpha_dummy_050 A) (nb090_alpha_dummy_053 h) (nb090_wpp_notmem_0132 A) (nb090_wpp_notmem_0133 h) (TEnvFresh.consFresh (nb090_alpha_dummy_049 A) (nb090_alpha_dummy_052 h) (nb090_wpp_notmem_0134 A) (nb090_wpp_notmem_0135 h) (TEnvFresh.consFresh (nb090_alpha_dummy_055 A) (nb090_alpha_dummy_056 h) (nb090_wpp_notmem_0136 A) (nb090_wpp_notmem_0137 h) (TEnvFresh.consFresh (nb090_alpha_dummy_047 A) (nb090_alpha_dummy_048 h) (nb090_wpp_notmem_0138 A) (nb090_wpp_notmem_0139 h) (TEnvFresh.consFresh (nb090_alpha_dummy_045 A) (nb090_alpha_dummy_046 h) (nb090_wpp_notmem_0140 A) (nb090_wpp_notmem_0141 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0142 A) (nb090_wpp_notmem_0143 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0020 A) (nb090_wpp_notmem_0021 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0022 A) (nb090_wpp_notmem_0023 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0024 A) (nb090_wpp_notmem_0025 v u A h) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))))

noncomputable def nb090_wpp_refl_0011 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_073 A), (nb090_alpha_dummy_076 h)), ((nb090_alpha_dummy_072 A), (nb090_alpha_dummy_075 h)), ((nb090_alpha_dummy_071 A), (nb090_alpha_dummy_074 h)), ((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)), ((nb090_alpha_dummy_065 A), (nb090_alpha_dummy_067 h)), ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)), ((nb090_alpha_dummy_091 A), (nb090_alpha_dummy_092 h)), ((nb090_alpha_dummy_089 A), (nb090_alpha_dummy_090 h)), ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)), ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_087 A), (nb090_alpha_dummy_088 h)), ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0011 v u A h)

theorem nb090_wpp_notmem_0208 (A : Class) : (nb090_alpha_dummy_091 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_091, fv_syn_c0] using (nb090_compact_fv_empty_0064 A)

theorem nb090_wpp_notmem_0209 (h : Var) : (nb090_alpha_dummy_092 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_092, fv_syn_c0] using (nb090_compact_fv_empty_0065 h)

theorem nb090_wpp_notmem_0210 (A : Class) : (nb090_alpha_dummy_089 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_089, fv_syn_c0] using (nb090_compact_fv_empty_0066 A)

theorem nb090_wpp_notmem_0211 (h : Var) : (nb090_alpha_dummy_090 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_090, fv_syn_c0] using (nb090_compact_fv_empty_0067 h)

theorem nb090_wpp_notmem_0212 (A : Class) : (nb090_alpha_dummy_087 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_087, fv_syn_c0] using (nb090_compact_fv_empty_0068 A)

theorem nb090_wpp_notmem_0213 (h : Var) : (nb090_alpha_dummy_088 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_088, fv_syn_c0] using (nb090_compact_fv_empty_0069 h)

theorem nb090_compact_envfresh_0012 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_073 A), (nb090_alpha_dummy_076 h)), ((nb090_alpha_dummy_072 A), (nb090_alpha_dummy_075 h)), ((nb090_alpha_dummy_071 A), (nb090_alpha_dummy_074 h)), ((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)), ((nb090_alpha_dummy_065 A), (nb090_alpha_dummy_067 h)), ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)), ((nb090_alpha_dummy_091 A), (nb090_alpha_dummy_092 h)), ((nb090_alpha_dummy_089 A), (nb090_alpha_dummy_090 h)), ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)), ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_087 A), (nb090_alpha_dummy_088 h)), ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_073 A) (nb090_alpha_dummy_076 h) (nb090_wpp_notmem_0144 A) (nb090_wpp_notmem_0145 h) (TEnvFresh.consFresh (nb090_alpha_dummy_072 A) (nb090_alpha_dummy_075 h) (nb090_wpp_notmem_0146 A) (nb090_wpp_notmem_0147 h) (TEnvFresh.consFresh (nb090_alpha_dummy_071 A) (nb090_alpha_dummy_074 h) (nb090_wpp_notmem_0148 A) (nb090_wpp_notmem_0149 h) (TEnvFresh.consFresh (nb090_alpha_dummy_069 A) (nb090_alpha_dummy_070 h) (nb090_wpp_notmem_0150 A) (nb090_wpp_notmem_0151 h) (TEnvFresh.consFresh (nb090_alpha_dummy_065 A) (nb090_alpha_dummy_067 h) (nb090_wpp_notmem_0152 A) (nb090_wpp_notmem_0153 h) (TEnvFresh.consFresh (nb090_alpha_dummy_066 A) (nb090_alpha_dummy_068 h) (nb090_wpp_notmem_0154 A) (nb090_wpp_notmem_0155 h) (TEnvFresh.consFresh (nb090_alpha_dummy_091 A) (nb090_alpha_dummy_092 h) (nb090_wpp_notmem_0208 A) (nb090_wpp_notmem_0209 h) (TEnvFresh.consFresh (nb090_alpha_dummy_089 A) (nb090_alpha_dummy_090 h) (nb090_wpp_notmem_0210 A) (nb090_wpp_notmem_0211 h) (TEnvFresh.consFresh (nb090_alpha_dummy_058 A) (nb090_alpha_dummy_060 h) (nb090_wpp_notmem_0156 A) (nb090_wpp_notmem_0157 h) (TEnvFresh.consFresh (nb090_alpha_dummy_057 A) (nb090_alpha_dummy_059 h) (nb090_wpp_notmem_0158 A) (nb090_wpp_notmem_0159 h) (TEnvFresh.consFresh (nb090_alpha_dummy_087 A) (nb090_alpha_dummy_088 h) (nb090_wpp_notmem_0212 A) (nb090_wpp_notmem_0213 h) (TEnvFresh.consFresh (nb090_alpha_dummy_061 A) (nb090_alpha_dummy_062 h) (nb090_wpp_notmem_0162 A) (nb090_wpp_notmem_0163 h) (TEnvFresh.consFresh (nb090_alpha_dummy_050 A) (nb090_alpha_dummy_053 h) (nb090_wpp_notmem_0164 A) (nb090_wpp_notmem_0165 h) (TEnvFresh.consFresh (nb090_alpha_dummy_049 A) (nb090_alpha_dummy_052 h) (nb090_wpp_notmem_0166 A) (nb090_wpp_notmem_0167 h) (TEnvFresh.consFresh (nb090_alpha_dummy_055 A) (nb090_alpha_dummy_056 h) (nb090_wpp_notmem_0168 A) (nb090_wpp_notmem_0169 h) (TEnvFresh.consFresh (nb090_alpha_dummy_047 A) (nb090_alpha_dummy_048 h) (nb090_wpp_notmem_0170 A) (nb090_wpp_notmem_0171 h) (TEnvFresh.consFresh (nb090_alpha_dummy_045 A) (nb090_alpha_dummy_046 h) (nb090_wpp_notmem_0172 A) (nb090_wpp_notmem_0173 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0174 A) (nb090_wpp_notmem_0175 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0046 A) (nb090_wpp_notmem_0047 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0048 A) (nb090_wpp_notmem_0049 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0050 A) (nb090_wpp_notmem_0051 v u A h) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))))

noncomputable def nb090_wpp_refl_0012 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_073 A), (nb090_alpha_dummy_076 h)), ((nb090_alpha_dummy_072 A), (nb090_alpha_dummy_075 h)), ((nb090_alpha_dummy_071 A), (nb090_alpha_dummy_074 h)), ((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)), ((nb090_alpha_dummy_065 A), (nb090_alpha_dummy_067 h)), ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)), ((nb090_alpha_dummy_091 A), (nb090_alpha_dummy_092 h)), ((nb090_alpha_dummy_089 A), (nb090_alpha_dummy_090 h)), ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)), ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_087 A), (nb090_alpha_dummy_088 h)), ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0012 v u A h)

theorem nb090_wpp_notmem_0214 (A : Class) : (nb090_alpha_dummy_091 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_091, fv_syn_cnnc] using (nb090_compact_fv_empty_0064 A)

theorem nb090_wpp_notmem_0215 (h : Var) : (nb090_alpha_dummy_092 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_092, fv_syn_cnnc] using (nb090_compact_fv_empty_0065 h)

theorem nb090_wpp_notmem_0216 (A : Class) : (nb090_alpha_dummy_089 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_089, fv_syn_cnnc] using (nb090_compact_fv_empty_0066 A)

theorem nb090_wpp_notmem_0217 (h : Var) : (nb090_alpha_dummy_090 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_090, fv_syn_cnnc] using (nb090_compact_fv_empty_0067 h)

theorem nb090_wpp_notmem_0218 (A : Class) : (nb090_alpha_dummy_087 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_087, fv_syn_cnnc] using (nb090_compact_fv_empty_0068 A)

theorem nb090_wpp_notmem_0219 (h : Var) : (nb090_alpha_dummy_088 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_088, fv_syn_cnnc] using (nb090_compact_fv_empty_0069 h)

theorem nb090_compact_envfresh_0013 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)), ((nb090_alpha_dummy_065 A), (nb090_alpha_dummy_067 h)), ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)), ((nb090_alpha_dummy_091 A), (nb090_alpha_dummy_092 h)), ((nb090_alpha_dummy_089 A), (nb090_alpha_dummy_090 h)), ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)), ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_087 A), (nb090_alpha_dummy_088 h)), ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_069 A) (nb090_alpha_dummy_070 h) (nb090_wpp_notmem_0176 A) (nb090_wpp_notmem_0177 h) (TEnvFresh.consFresh (nb090_alpha_dummy_065 A) (nb090_alpha_dummy_067 h) (nb090_wpp_notmem_0178 A) (nb090_wpp_notmem_0179 h) (TEnvFresh.consFresh (nb090_alpha_dummy_066 A) (nb090_alpha_dummy_068 h) (nb090_wpp_notmem_0180 A) (nb090_wpp_notmem_0181 h) (TEnvFresh.consFresh (nb090_alpha_dummy_091 A) (nb090_alpha_dummy_092 h) (nb090_wpp_notmem_0214 A) (nb090_wpp_notmem_0215 h) (TEnvFresh.consFresh (nb090_alpha_dummy_089 A) (nb090_alpha_dummy_090 h) (nb090_wpp_notmem_0216 A) (nb090_wpp_notmem_0217 h) (TEnvFresh.consFresh (nb090_alpha_dummy_058 A) (nb090_alpha_dummy_060 h) (nb090_wpp_notmem_0182 A) (nb090_wpp_notmem_0183 h) (TEnvFresh.consFresh (nb090_alpha_dummy_057 A) (nb090_alpha_dummy_059 h) (nb090_wpp_notmem_0184 A) (nb090_wpp_notmem_0185 h) (TEnvFresh.consFresh (nb090_alpha_dummy_087 A) (nb090_alpha_dummy_088 h) (nb090_wpp_notmem_0218 A) (nb090_wpp_notmem_0219 h) (TEnvFresh.consFresh (nb090_alpha_dummy_061 A) (nb090_alpha_dummy_062 h) (nb090_wpp_notmem_0188 A) (nb090_wpp_notmem_0189 h) (TEnvFresh.consFresh (nb090_alpha_dummy_050 A) (nb090_alpha_dummy_053 h) (nb090_wpp_notmem_0190 A) (nb090_wpp_notmem_0191 h) (TEnvFresh.consFresh (nb090_alpha_dummy_049 A) (nb090_alpha_dummy_052 h) (nb090_wpp_notmem_0192 A) (nb090_wpp_notmem_0193 h) (TEnvFresh.consFresh (nb090_alpha_dummy_055 A) (nb090_alpha_dummy_056 h) (nb090_wpp_notmem_0194 A) (nb090_wpp_notmem_0195 h) (TEnvFresh.consFresh (nb090_alpha_dummy_047 A) (nb090_alpha_dummy_048 h) (nb090_wpp_notmem_0196 A) (nb090_wpp_notmem_0197 h) (TEnvFresh.consFresh (nb090_alpha_dummy_045 A) (nb090_alpha_dummy_046 h) (nb090_wpp_notmem_0198 A) (nb090_wpp_notmem_0199 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0200 A) (nb090_wpp_notmem_0201 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0066 A) (nb090_wpp_notmem_0067 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0068 A) (nb090_wpp_notmem_0069 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0070 A) (nb090_wpp_notmem_0071 v u A h) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))))

noncomputable def nb090_wpp_refl_0013 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)), ((nb090_alpha_dummy_065 A), (nb090_alpha_dummy_067 h)), ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)), ((nb090_alpha_dummy_091 A), (nb090_alpha_dummy_092 h)), ((nb090_alpha_dummy_089 A), (nb090_alpha_dummy_090 h)), ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)), ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_087 A), (nb090_alpha_dummy_088 h)), ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0013 v u A h)

noncomputable def nb090_split_alpha_0002 (v : Var) (u : Var) (A : Class) (h : Var) : TAlphaWff [((nb090_alpha_dummy_089 A), (nb090_alpha_dummy_090 h)), ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)), ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_087 A), (nb090_alpha_dummy_088 h)), ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (Wff.classMem (Class.cv (nb090_alpha_dummy_089 A)) (syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))) (Wff.classMem (Class.cv (nb090_alpha_dummy_090 h)) (syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0052 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0053 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0052 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0053 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0082 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0083 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0080 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0081 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_058 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_060 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0056 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0057 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0056 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0057 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0054 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0055 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_073 A), (nb090_alpha_dummy_076 h)), ((nb090_alpha_dummy_072 A), (nb090_alpha_dummy_075 h)), ((nb090_alpha_dummy_071 A), (nb090_alpha_dummy_074 h)), ((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)), ((nb090_alpha_dummy_065 A), (nb090_alpha_dummy_067 h)), ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)), ((nb090_alpha_dummy_091 A), (nb090_alpha_dummy_092 h)), ((nb090_alpha_dummy_089 A), (nb090_alpha_dummy_090 h)), ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)), ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_087 A), (nb090_alpha_dummy_088 h)), ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0011 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0060 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0061 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0058 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0059 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0064 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0065 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0062 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0063 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0060 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0061 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0058 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0059 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0064 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0065 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0062 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0063 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_073 A), (nb090_alpha_dummy_076 h)), ((nb090_alpha_dummy_072 A), (nb090_alpha_dummy_075 h)), ((nb090_alpha_dummy_071 A), (nb090_alpha_dummy_074 h)), ((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)), ((nb090_alpha_dummy_065 A), (nb090_alpha_dummy_067 h)), ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)), ((nb090_alpha_dummy_091 A), (nb090_alpha_dummy_092 h)), ((nb090_alpha_dummy_089 A), (nb090_alpha_dummy_090 h)), ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)), ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_087 A), (nb090_alpha_dummy_088 h)), ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0012 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0068 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0069 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0066 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0067 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0068 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0069 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0066 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0067 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0072 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0073 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0070 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0071 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0072 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0073 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0070 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0071 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0054 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0055 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)), ((nb090_alpha_dummy_065 A), (nb090_alpha_dummy_067 h)), ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)), ((nb090_alpha_dummy_091 A), (nb090_alpha_dummy_092 h)), ((nb090_alpha_dummy_089 A), (nb090_alpha_dummy_090 h)), ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)), ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_087 A), (nb090_alpha_dummy_088 h)), ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0013 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0054 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0055 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0054 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0055 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)), ((nb090_alpha_dummy_065 A), (nb090_alpha_dummy_067 h)), ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)), ((nb090_alpha_dummy_091 A), (nb090_alpha_dummy_092 h)), ((nb090_alpha_dummy_089 A), (nb090_alpha_dummy_090 h)), ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)), ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_087 A), (nb090_alpha_dummy_088 h)), ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0013 v u A h)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0052 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0053 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0052 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0053 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0082 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0083 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0080 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0081 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_058 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_060 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0056 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0057 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0056 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0057 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0054 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0055 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_073 A), (nb090_alpha_dummy_076 h)), ((nb090_alpha_dummy_072 A), (nb090_alpha_dummy_075 h)), ((nb090_alpha_dummy_071 A), (nb090_alpha_dummy_074 h)), ((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)), ((nb090_alpha_dummy_065 A), (nb090_alpha_dummy_067 h)), ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)), ((nb090_alpha_dummy_091 A), (nb090_alpha_dummy_092 h)), ((nb090_alpha_dummy_089 A), (nb090_alpha_dummy_090 h)), ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)), ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_087 A), (nb090_alpha_dummy_088 h)), ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0011 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0060 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0061 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0058 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0059 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0064 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0065 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0062 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0063 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0060 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0061 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0058 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0059 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0064 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0065 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0062 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0063 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_073 A), (nb090_alpha_dummy_076 h)), ((nb090_alpha_dummy_072 A), (nb090_alpha_dummy_075 h)), ((nb090_alpha_dummy_071 A), (nb090_alpha_dummy_074 h)), ((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)), ((nb090_alpha_dummy_065 A), (nb090_alpha_dummy_067 h)), ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)), ((nb090_alpha_dummy_091 A), (nb090_alpha_dummy_092 h)), ((nb090_alpha_dummy_089 A), (nb090_alpha_dummy_090 h)), ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)), ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_087 A), (nb090_alpha_dummy_088 h)), ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0012 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0068 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0069 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0066 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0067 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0068 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0069 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0066 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0067 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0072 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0073 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0070 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0071 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0072 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0073 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0070 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0071 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0054 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0055 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)), ((nb090_alpha_dummy_065 A), (nb090_alpha_dummy_067 h)), ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)), ((nb090_alpha_dummy_091 A), (nb090_alpha_dummy_092 h)), ((nb090_alpha_dummy_089 A), (nb090_alpha_dummy_090 h)), ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)), ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_087 A), (nb090_alpha_dummy_088 h)), ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0013 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0054 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0055 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0054 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0055 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)), ((nb090_alpha_dummy_065 A), (nb090_alpha_dummy_067 h)), ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)), ((nb090_alpha_dummy_091 A), (nb090_alpha_dummy_092 h)), ((nb090_alpha_dummy_089 A), (nb090_alpha_dummy_090 h)), ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)), ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_087 A), (nb090_alpha_dummy_088 h)), ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0013 v u A h))))))))))))))))))))))))

theorem nb090_wpp_notmem_0220 (A : Class) : (nb090_alpha_dummy_089 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_089, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0066 A)

theorem nb090_wpp_notmem_0221 (h : Var) : (nb090_alpha_dummy_090 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_090, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0067 h)

theorem nb090_wpp_notmem_0222 (A : Class) : (nb090_alpha_dummy_058 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_058, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0044 A)

theorem nb090_wpp_notmem_0223 (h : Var) : (nb090_alpha_dummy_060 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_060, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0045 h)

theorem nb090_wpp_notmem_0224 (A : Class) : (nb090_alpha_dummy_057 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_057, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0046 A)

theorem nb090_wpp_notmem_0225 (h : Var) : (nb090_alpha_dummy_059 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_059, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0047 h)

theorem nb090_wpp_notmem_0226 (A : Class) : (nb090_alpha_dummy_087 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_087, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0068 A)

theorem nb090_wpp_notmem_0227 (h : Var) : (nb090_alpha_dummy_088 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_088, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0069 h)

theorem nb090_wpp_notmem_0228 (A : Class) : (nb090_alpha_dummy_061 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_061, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0050 A)

theorem nb090_wpp_notmem_0229 (h : Var) : (nb090_alpha_dummy_062 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_062, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0051 h)

theorem nb090_wpp_notmem_0230 (A : Class) : (nb090_alpha_dummy_050 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_050, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0052 A)

theorem nb090_wpp_notmem_0231 (h : Var) : (nb090_alpha_dummy_053 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_053, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0053 h)

theorem nb090_wpp_notmem_0232 (A : Class) : (nb090_alpha_dummy_049 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_049, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0054 A)

theorem nb090_wpp_notmem_0233 (h : Var) : (nb090_alpha_dummy_052 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_052, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0055 h)

theorem nb090_wpp_notmem_0234 (A : Class) : (nb090_alpha_dummy_055 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_055, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0056 A)

theorem nb090_wpp_notmem_0235 (h : Var) : (nb090_alpha_dummy_056 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_056, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0057 h)

theorem nb090_wpp_notmem_0236 (A : Class) : (nb090_alpha_dummy_047 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_047, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0058 A)

theorem nb090_wpp_notmem_0237 (h : Var) : (nb090_alpha_dummy_048 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_048, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0059 h)

theorem nb090_wpp_notmem_0238 (A : Class) : (nb090_alpha_dummy_045 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_045, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0060 A)

theorem nb090_wpp_notmem_0239 (h : Var) : (nb090_alpha_dummy_046 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_046, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0061 h)

theorem nb090_wpp_notmem_0240 (A : Class) : (nb090_alpha_dummy_000 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_000, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0062 A)

theorem nb090_wpp_notmem_0241 (h : Var) : h ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0063 h)

theorem nb090_compact_envfresh_0014 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_089 A), (nb090_alpha_dummy_090 h)), ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)), ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_087 A), (nb090_alpha_dummy_088 h)), ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_089 A) (nb090_alpha_dummy_090 h) (nb090_wpp_notmem_0220 A) (nb090_wpp_notmem_0221 h) (TEnvFresh.consFresh (nb090_alpha_dummy_058 A) (nb090_alpha_dummy_060 h) (nb090_wpp_notmem_0222 A) (nb090_wpp_notmem_0223 h) (TEnvFresh.consFresh (nb090_alpha_dummy_057 A) (nb090_alpha_dummy_059 h) (nb090_wpp_notmem_0224 A) (nb090_wpp_notmem_0225 h) (TEnvFresh.consFresh (nb090_alpha_dummy_087 A) (nb090_alpha_dummy_088 h) (nb090_wpp_notmem_0226 A) (nb090_wpp_notmem_0227 h) (TEnvFresh.consFresh (nb090_alpha_dummy_061 A) (nb090_alpha_dummy_062 h) (nb090_wpp_notmem_0228 A) (nb090_wpp_notmem_0229 h) (TEnvFresh.consFresh (nb090_alpha_dummy_050 A) (nb090_alpha_dummy_053 h) (nb090_wpp_notmem_0230 A) (nb090_wpp_notmem_0231 h) (TEnvFresh.consFresh (nb090_alpha_dummy_049 A) (nb090_alpha_dummy_052 h) (nb090_wpp_notmem_0232 A) (nb090_wpp_notmem_0233 h) (TEnvFresh.consFresh (nb090_alpha_dummy_055 A) (nb090_alpha_dummy_056 h) (nb090_wpp_notmem_0234 A) (nb090_wpp_notmem_0235 h) (TEnvFresh.consFresh (nb090_alpha_dummy_047 A) (nb090_alpha_dummy_048 h) (nb090_wpp_notmem_0236 A) (nb090_wpp_notmem_0237 h) (TEnvFresh.consFresh (nb090_alpha_dummy_045 A) (nb090_alpha_dummy_046 h) (nb090_wpp_notmem_0238 A) (nb090_wpp_notmem_0239 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0240 A) (nb090_wpp_notmem_0241 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0100 A) (nb090_wpp_notmem_0101 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0102 A) (nb090_wpp_notmem_0103 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0104 A) (nb090_wpp_notmem_0105 v u A h) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))))))

noncomputable def nb090_wpp_refl_0014 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_089 A), (nb090_alpha_dummy_090 h)), ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)), ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_087 A), (nb090_alpha_dummy_088 h)), ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0014 v u A h)

theorem nb090_compact_fv_empty_0070 (A : Class) : (nb090_alpha_dummy_109 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0242 (A : Class) : (nb090_alpha_dummy_109 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_109, fv_syn_c1c] using (nb090_compact_fv_empty_0070 A)

theorem nb090_compact_fv_empty_0071 (h : Var) : (nb090_alpha_dummy_112 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0243 (h : Var) : (nb090_alpha_dummy_112 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_112, fv_syn_c1c] using (nb090_compact_fv_empty_0071 h)

theorem nb090_compact_fv_empty_0072 (A : Class) : (nb090_alpha_dummy_108 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0244 (A : Class) : (nb090_alpha_dummy_108 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_108, fv_syn_c1c] using (nb090_compact_fv_empty_0072 A)

theorem nb090_compact_fv_empty_0073 (h : Var) : (nb090_alpha_dummy_111 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0245 (h : Var) : (nb090_alpha_dummy_111 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_111, fv_syn_c1c] using (nb090_compact_fv_empty_0073 h)

theorem nb090_compact_fv_empty_0074 (A : Class) : (nb090_alpha_dummy_107 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0246 (A : Class) : (nb090_alpha_dummy_107 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_107, fv_syn_c1c] using (nb090_compact_fv_empty_0074 A)

theorem nb090_compact_fv_empty_0075 (h : Var) : (nb090_alpha_dummy_110 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0247 (h : Var) : (nb090_alpha_dummy_110 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_110, fv_syn_c1c] using (nb090_compact_fv_empty_0075 h)

theorem nb090_compact_fv_empty_0076 (A : Class) : (nb090_alpha_dummy_105 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0248 (A : Class) : (nb090_alpha_dummy_105 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_105, fv_syn_c1c] using (nb090_compact_fv_empty_0076 A)

theorem nb090_compact_fv_empty_0077 (h : Var) : (nb090_alpha_dummy_106 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0249 (h : Var) : (nb090_alpha_dummy_106 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_106, fv_syn_c1c] using (nb090_compact_fv_empty_0077 h)

theorem nb090_compact_fv_empty_0078 (A : Class) : (nb090_alpha_dummy_101 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0250 (A : Class) : (nb090_alpha_dummy_101 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_101, fv_syn_c1c] using (nb090_compact_fv_empty_0078 A)

theorem nb090_compact_fv_empty_0079 (h : Var) : (nb090_alpha_dummy_103 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0251 (h : Var) : (nb090_alpha_dummy_103 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_103, fv_syn_c1c] using (nb090_compact_fv_empty_0079 h)

theorem nb090_compact_fv_empty_0080 (A : Class) : (nb090_alpha_dummy_102 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0252 (A : Class) : (nb090_alpha_dummy_102 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_102, fv_syn_c1c] using (nb090_compact_fv_empty_0080 A)

theorem nb090_compact_fv_empty_0081 (h : Var) : (nb090_alpha_dummy_104 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0253 (h : Var) : (nb090_alpha_dummy_104 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_104, fv_syn_c1c] using (nb090_compact_fv_empty_0081 h)

theorem nb090_compact_fv_empty_0082 (A : Class) : (nb090_alpha_dummy_094 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0254 (A : Class) : (nb090_alpha_dummy_094 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_094, fv_syn_c1c] using (nb090_compact_fv_empty_0082 A)

theorem nb090_compact_fv_empty_0083 (h : Var) : (nb090_alpha_dummy_096 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0255 (h : Var) : (nb090_alpha_dummy_096 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_096, fv_syn_c1c] using (nb090_compact_fv_empty_0083 h)

theorem nb090_compact_fv_empty_0084 (A : Class) : (nb090_alpha_dummy_093 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0256 (A : Class) : (nb090_alpha_dummy_093 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_093, fv_syn_c1c] using (nb090_compact_fv_empty_0084 A)

theorem nb090_compact_fv_empty_0085 (h : Var) : (nb090_alpha_dummy_095 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0257 (h : Var) : (nb090_alpha_dummy_095 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_095, fv_syn_c1c] using (nb090_compact_fv_empty_0085 h)

theorem nb090_compact_fv_empty_0086 (A : Class) : (nb090_alpha_dummy_099 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0258 (A : Class) : (nb090_alpha_dummy_099 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_099, fv_syn_c1c] using (nb090_compact_fv_empty_0086 A)

theorem nb090_compact_fv_empty_0087 (h : Var) : (nb090_alpha_dummy_100 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0259 (h : Var) : (nb090_alpha_dummy_100 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_100, fv_syn_c1c] using (nb090_compact_fv_empty_0087 h)

theorem nb090_compact_fv_empty_0088 (A : Class) : (nb090_alpha_dummy_097 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0260 (A : Class) : (nb090_alpha_dummy_097 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_097, fv_syn_c1c] using (nb090_compact_fv_empty_0088 A)

theorem nb090_compact_fv_empty_0089 (h : Var) : (nb090_alpha_dummy_098 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0261 (h : Var) : (nb090_alpha_dummy_098 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_098, fv_syn_c1c] using (nb090_compact_fv_empty_0089 h)

theorem nb090_compact_fv_empty_0090 (A : Class) : (nb090_alpha_dummy_051 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0262 (A : Class) : (nb090_alpha_dummy_051 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_051, fv_syn_c1c] using (nb090_compact_fv_empty_0090 A)

theorem nb090_compact_fv_empty_0091 (h : Var) : (nb090_alpha_dummy_054 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0263 (h : Var) : (nb090_alpha_dummy_054 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_054, fv_syn_c1c] using (nb090_compact_fv_empty_0091 h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
