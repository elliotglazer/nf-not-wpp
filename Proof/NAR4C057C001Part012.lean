import NAR4C057C001Part011

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

theorem nb057_wpp_notmem_0341 (f : Var) : (nb057_alpha_dummy_126 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_126, fv_syn_c1c] using (nb057_compact_fv_empty_0119 f)

theorem nb057_compact_fv_empty_0120 : (nb057_alpha_dummy_128) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0342 : (nb057_alpha_dummy_128) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_128, fv_syn_c1c] using (nb057_compact_fv_empty_0120)

theorem nb057_compact_fv_empty_0121 (f : Var) : (nb057_alpha_dummy_129 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0343 (f : Var) : (nb057_alpha_dummy_129 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_129, fv_syn_c1c] using (nb057_compact_fv_empty_0121 f)

theorem nb057_compact_envfresh_0021 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)), ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)), ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)), ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)), ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)), ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_136), (nb057_alpha_dummy_137 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_146) (nb057_alpha_dummy_149 f) (nb057_wpp_notmem_0318) (nb057_wpp_notmem_0319 f) (TEnvFresh.consFresh (nb057_alpha_dummy_145) (nb057_alpha_dummy_148 f) (nb057_wpp_notmem_0320) (nb057_wpp_notmem_0321 f) (TEnvFresh.consFresh (nb057_alpha_dummy_144) (nb057_alpha_dummy_147 f) (nb057_wpp_notmem_0322) (nb057_wpp_notmem_0323 f) (TEnvFresh.consFresh (nb057_alpha_dummy_142) (nb057_alpha_dummy_143 f) (nb057_wpp_notmem_0324) (nb057_wpp_notmem_0325 f) (TEnvFresh.consFresh (nb057_alpha_dummy_138) (nb057_alpha_dummy_140 f) (nb057_wpp_notmem_0326) (nb057_wpp_notmem_0327 f) (TEnvFresh.consFresh (nb057_alpha_dummy_139) (nb057_alpha_dummy_141 f) (nb057_wpp_notmem_0328) (nb057_wpp_notmem_0329 f) (TEnvFresh.consFresh (nb057_alpha_dummy_131) (nb057_alpha_dummy_133 f) (nb057_wpp_notmem_0330) (nb057_wpp_notmem_0331 f) (TEnvFresh.consFresh (nb057_alpha_dummy_130) (nb057_alpha_dummy_132 f) (nb057_wpp_notmem_0332) (nb057_wpp_notmem_0333 f) (TEnvFresh.consFresh (nb057_alpha_dummy_136) (nb057_alpha_dummy_137 f) (nb057_wpp_notmem_0334) (nb057_wpp_notmem_0335 f) (TEnvFresh.consFresh (nb057_alpha_dummy_134) (nb057_alpha_dummy_135 f) (nb057_wpp_notmem_0336) (nb057_wpp_notmem_0337 f) (TEnvFresh.consFresh (nb057_alpha_dummy_125) (nb057_alpha_dummy_127 f) (nb057_wpp_notmem_0338) (nb057_wpp_notmem_0339 f) (TEnvFresh.consFresh (nb057_alpha_dummy_124) (nb057_alpha_dummy_126 f) (nb057_wpp_notmem_0340) (nb057_wpp_notmem_0341 f) (TEnvFresh.consFresh (nb057_alpha_dummy_128) (nb057_alpha_dummy_129 f) (nb057_wpp_notmem_0342) (nb057_wpp_notmem_0343 f) (TEnvFresh.consFresh (nb057_alpha_dummy_046) (nb057_alpha_dummy_049 f) (nb057_wpp_notmem_0248) (nb057_wpp_notmem_0249 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0126) (nb057_wpp_notmem_0127 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0128) (nb057_wpp_notmem_0129 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0130) (nb057_wpp_notmem_0131 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0132) (nb057_wpp_notmem_0133 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0134) (nb057_wpp_notmem_0135 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0020) (nb057_wpp_notmem_0021 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0022) (nb057_wpp_notmem_0023 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0024) (nb057_wpp_notmem_0025 f a) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))))

noncomputable def nb057_wpp_refl_0021 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)), ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)), ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)), ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)), ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)), ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_136), (nb057_alpha_dummy_137 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0021 f a)

theorem nb057_wpp_notmem_0344 : (nb057_alpha_dummy_146) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_146, fv_syn_c0] using (nb057_compact_fv_empty_0096)

theorem nb057_wpp_notmem_0345 (f : Var) : (nb057_alpha_dummy_149 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_149, fv_syn_c0] using (nb057_compact_fv_empty_0097 f)

theorem nb057_wpp_notmem_0346 : (nb057_alpha_dummy_145) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_145, fv_syn_c0] using (nb057_compact_fv_empty_0098)

theorem nb057_wpp_notmem_0347 (f : Var) : (nb057_alpha_dummy_148 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_148, fv_syn_c0] using (nb057_compact_fv_empty_0099 f)

theorem nb057_wpp_notmem_0348 : (nb057_alpha_dummy_144) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_144, fv_syn_c0] using (nb057_compact_fv_empty_0100)

theorem nb057_wpp_notmem_0349 (f : Var) : (nb057_alpha_dummy_147 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_147, fv_syn_c0] using (nb057_compact_fv_empty_0101 f)

theorem nb057_wpp_notmem_0350 : (nb057_alpha_dummy_142) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_142, fv_syn_c0] using (nb057_compact_fv_empty_0102)

theorem nb057_wpp_notmem_0351 (f : Var) : (nb057_alpha_dummy_143 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_143, fv_syn_c0] using (nb057_compact_fv_empty_0103 f)

theorem nb057_wpp_notmem_0352 : (nb057_alpha_dummy_138) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_138, fv_syn_c0] using (nb057_compact_fv_empty_0104)

theorem nb057_wpp_notmem_0353 (f : Var) : (nb057_alpha_dummy_140 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_140, fv_syn_c0] using (nb057_compact_fv_empty_0105 f)

theorem nb057_wpp_notmem_0354 : (nb057_alpha_dummy_139) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_139, fv_syn_c0] using (nb057_compact_fv_empty_0106)

theorem nb057_wpp_notmem_0355 (f : Var) : (nb057_alpha_dummy_141 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_141, fv_syn_c0] using (nb057_compact_fv_empty_0107 f)

theorem nb057_wpp_notmem_0356 : (nb057_alpha_dummy_131) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_131, fv_syn_c0] using (nb057_compact_fv_empty_0108)

theorem nb057_wpp_notmem_0357 (f : Var) : (nb057_alpha_dummy_133 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_133, fv_syn_c0] using (nb057_compact_fv_empty_0109 f)

theorem nb057_wpp_notmem_0358 : (nb057_alpha_dummy_130) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_130, fv_syn_c0] using (nb057_compact_fv_empty_0110)

theorem nb057_wpp_notmem_0359 (f : Var) : (nb057_alpha_dummy_132 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_132, fv_syn_c0] using (nb057_compact_fv_empty_0111 f)

theorem nb057_wpp_notmem_0360 : (nb057_alpha_dummy_136) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_136, fv_syn_c0] using (nb057_compact_fv_empty_0112)

theorem nb057_wpp_notmem_0361 (f : Var) : (nb057_alpha_dummy_137 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_137, fv_syn_c0] using (nb057_compact_fv_empty_0113 f)

theorem nb057_wpp_notmem_0362 : (nb057_alpha_dummy_134) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_134, fv_syn_c0] using (nb057_compact_fv_empty_0114)

theorem nb057_wpp_notmem_0363 (f : Var) : (nb057_alpha_dummy_135 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_135, fv_syn_c0] using (nb057_compact_fv_empty_0115 f)

theorem nb057_wpp_notmem_0364 : (nb057_alpha_dummy_125) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_125, fv_syn_c0] using (nb057_compact_fv_empty_0116)

theorem nb057_wpp_notmem_0365 (f : Var) : (nb057_alpha_dummy_127 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_127, fv_syn_c0] using (nb057_compact_fv_empty_0117 f)

theorem nb057_wpp_notmem_0366 : (nb057_alpha_dummy_124) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_124, fv_syn_c0] using (nb057_compact_fv_empty_0118)

theorem nb057_wpp_notmem_0367 (f : Var) : (nb057_alpha_dummy_126 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_126, fv_syn_c0] using (nb057_compact_fv_empty_0119 f)

theorem nb057_wpp_notmem_0368 : (nb057_alpha_dummy_128) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_128, fv_syn_c0] using (nb057_compact_fv_empty_0120)

theorem nb057_wpp_notmem_0369 (f : Var) : (nb057_alpha_dummy_129 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_129, fv_syn_c0] using (nb057_compact_fv_empty_0121 f)

theorem nb057_compact_envfresh_0022 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)), ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)), ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)), ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)), ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)), ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_136), (nb057_alpha_dummy_137 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_146) (nb057_alpha_dummy_149 f) (nb057_wpp_notmem_0344) (nb057_wpp_notmem_0345 f) (TEnvFresh.consFresh (nb057_alpha_dummy_145) (nb057_alpha_dummy_148 f) (nb057_wpp_notmem_0346) (nb057_wpp_notmem_0347 f) (TEnvFresh.consFresh (nb057_alpha_dummy_144) (nb057_alpha_dummy_147 f) (nb057_wpp_notmem_0348) (nb057_wpp_notmem_0349 f) (TEnvFresh.consFresh (nb057_alpha_dummy_142) (nb057_alpha_dummy_143 f) (nb057_wpp_notmem_0350) (nb057_wpp_notmem_0351 f) (TEnvFresh.consFresh (nb057_alpha_dummy_138) (nb057_alpha_dummy_140 f) (nb057_wpp_notmem_0352) (nb057_wpp_notmem_0353 f) (TEnvFresh.consFresh (nb057_alpha_dummy_139) (nb057_alpha_dummy_141 f) (nb057_wpp_notmem_0354) (nb057_wpp_notmem_0355 f) (TEnvFresh.consFresh (nb057_alpha_dummy_131) (nb057_alpha_dummy_133 f) (nb057_wpp_notmem_0356) (nb057_wpp_notmem_0357 f) (TEnvFresh.consFresh (nb057_alpha_dummy_130) (nb057_alpha_dummy_132 f) (nb057_wpp_notmem_0358) (nb057_wpp_notmem_0359 f) (TEnvFresh.consFresh (nb057_alpha_dummy_136) (nb057_alpha_dummy_137 f) (nb057_wpp_notmem_0360) (nb057_wpp_notmem_0361 f) (TEnvFresh.consFresh (nb057_alpha_dummy_134) (nb057_alpha_dummy_135 f) (nb057_wpp_notmem_0362) (nb057_wpp_notmem_0363 f) (TEnvFresh.consFresh (nb057_alpha_dummy_125) (nb057_alpha_dummy_127 f) (nb057_wpp_notmem_0364) (nb057_wpp_notmem_0365 f) (TEnvFresh.consFresh (nb057_alpha_dummy_124) (nb057_alpha_dummy_126 f) (nb057_wpp_notmem_0366) (nb057_wpp_notmem_0367 f) (TEnvFresh.consFresh (nb057_alpha_dummy_128) (nb057_alpha_dummy_129 f) (nb057_wpp_notmem_0368) (nb057_wpp_notmem_0369 f) (TEnvFresh.consFresh (nb057_alpha_dummy_046) (nb057_alpha_dummy_049 f) (nb057_wpp_notmem_0270) (nb057_wpp_notmem_0271 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0156) (nb057_wpp_notmem_0157 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0158) (nb057_wpp_notmem_0159 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0160) (nb057_wpp_notmem_0161 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0162) (nb057_wpp_notmem_0163 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0164) (nb057_wpp_notmem_0165 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0046) (nb057_wpp_notmem_0047 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0048) (nb057_wpp_notmem_0049 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0050) (nb057_wpp_notmem_0051 f a) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))))

noncomputable def nb057_wpp_refl_0022 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)), ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)), ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)), ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)), ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)), ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_136), (nb057_alpha_dummy_137 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0022 f a)

noncomputable def nb057_split_alpha_0015 (f : Var) (a : Var) : TAlphaWff [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)), ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)), ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)), ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)), ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)), ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_136), (nb057_alpha_dummy_137 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_144)) (syn_cun (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_148 f)) (Class.cv (nb057_alpha_dummy_149 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_147 f)) (syn_cun (Class.cv (nb057_alpha_dummy_148 f)) (Class.cv (nb057_alpha_dummy_149 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0140) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0141 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0138) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0139 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0144) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0145 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0142) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0143 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0140) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0141 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0138) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0139 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0144) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0145 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0142) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0143 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)), ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)), ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)), ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)), ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)), ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_136), (nb057_alpha_dummy_137 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_c0) (nb057_wpp_refl_0022 f a))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0148) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0149 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0147 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0148) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0149 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0147 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0152) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0153 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0150) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0151 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0152) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0153 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0150) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0151 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb057_wpp_notmem_0370 : (nb057_alpha_dummy_142) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_142, fv_syn_cnnc] using (nb057_compact_fv_empty_0102)

theorem nb057_wpp_notmem_0371 (f : Var) : (nb057_alpha_dummy_143 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_143, fv_syn_cnnc] using (nb057_compact_fv_empty_0103 f)

theorem nb057_wpp_notmem_0372 : (nb057_alpha_dummy_138) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_138, fv_syn_cnnc] using (nb057_compact_fv_empty_0104)

theorem nb057_wpp_notmem_0373 (f : Var) : (nb057_alpha_dummy_140 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_140, fv_syn_cnnc] using (nb057_compact_fv_empty_0105 f)

theorem nb057_wpp_notmem_0374 : (nb057_alpha_dummy_139) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_139, fv_syn_cnnc] using (nb057_compact_fv_empty_0106)

theorem nb057_wpp_notmem_0375 (f : Var) : (nb057_alpha_dummy_141 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_141, fv_syn_cnnc] using (nb057_compact_fv_empty_0107 f)

theorem nb057_wpp_notmem_0376 : (nb057_alpha_dummy_131) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_131, fv_syn_cnnc] using (nb057_compact_fv_empty_0108)

theorem nb057_wpp_notmem_0377 (f : Var) : (nb057_alpha_dummy_133 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_133, fv_syn_cnnc] using (nb057_compact_fv_empty_0109 f)

theorem nb057_wpp_notmem_0378 : (nb057_alpha_dummy_130) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_130, fv_syn_cnnc] using (nb057_compact_fv_empty_0110)

theorem nb057_wpp_notmem_0379 (f : Var) : (nb057_alpha_dummy_132 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_132, fv_syn_cnnc] using (nb057_compact_fv_empty_0111 f)

theorem nb057_wpp_notmem_0380 : (nb057_alpha_dummy_136) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_136, fv_syn_cnnc] using (nb057_compact_fv_empty_0112)

theorem nb057_wpp_notmem_0381 (f : Var) : (nb057_alpha_dummy_137 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_137, fv_syn_cnnc] using (nb057_compact_fv_empty_0113 f)

theorem nb057_wpp_notmem_0382 : (nb057_alpha_dummy_134) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_134, fv_syn_cnnc] using (nb057_compact_fv_empty_0114)

theorem nb057_wpp_notmem_0383 (f : Var) : (nb057_alpha_dummy_135 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_135, fv_syn_cnnc] using (nb057_compact_fv_empty_0115 f)

theorem nb057_wpp_notmem_0384 : (nb057_alpha_dummy_125) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_125, fv_syn_cnnc] using (nb057_compact_fv_empty_0116)

theorem nb057_wpp_notmem_0385 (f : Var) : (nb057_alpha_dummy_127 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_127, fv_syn_cnnc] using (nb057_compact_fv_empty_0117 f)

theorem nb057_wpp_notmem_0386 : (nb057_alpha_dummy_124) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_124, fv_syn_cnnc] using (nb057_compact_fv_empty_0118)

theorem nb057_wpp_notmem_0387 (f : Var) : (nb057_alpha_dummy_126 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_126, fv_syn_cnnc] using (nb057_compact_fv_empty_0119 f)

theorem nb057_wpp_notmem_0388 : (nb057_alpha_dummy_128) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_128, fv_syn_cnnc] using (nb057_compact_fv_empty_0120)

theorem nb057_wpp_notmem_0389 (f : Var) : (nb057_alpha_dummy_129 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_129, fv_syn_cnnc] using (nb057_compact_fv_empty_0121 f)

theorem nb057_compact_envfresh_0023 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)), ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)), ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_136), (nb057_alpha_dummy_137 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_142) (nb057_alpha_dummy_143 f) (nb057_wpp_notmem_0370) (nb057_wpp_notmem_0371 f) (TEnvFresh.consFresh (nb057_alpha_dummy_138) (nb057_alpha_dummy_140 f) (nb057_wpp_notmem_0372) (nb057_wpp_notmem_0373 f) (TEnvFresh.consFresh (nb057_alpha_dummy_139) (nb057_alpha_dummy_141 f) (nb057_wpp_notmem_0374) (nb057_wpp_notmem_0375 f) (TEnvFresh.consFresh (nb057_alpha_dummy_131) (nb057_alpha_dummy_133 f) (nb057_wpp_notmem_0376) (nb057_wpp_notmem_0377 f) (TEnvFresh.consFresh (nb057_alpha_dummy_130) (nb057_alpha_dummy_132 f) (nb057_wpp_notmem_0378) (nb057_wpp_notmem_0379 f) (TEnvFresh.consFresh (nb057_alpha_dummy_136) (nb057_alpha_dummy_137 f) (nb057_wpp_notmem_0380) (nb057_wpp_notmem_0381 f) (TEnvFresh.consFresh (nb057_alpha_dummy_134) (nb057_alpha_dummy_135 f) (nb057_wpp_notmem_0382) (nb057_wpp_notmem_0383 f) (TEnvFresh.consFresh (nb057_alpha_dummy_125) (nb057_alpha_dummy_127 f) (nb057_wpp_notmem_0384) (nb057_wpp_notmem_0385 f) (TEnvFresh.consFresh (nb057_alpha_dummy_124) (nb057_alpha_dummy_126 f) (nb057_wpp_notmem_0386) (nb057_wpp_notmem_0387 f) (TEnvFresh.consFresh (nb057_alpha_dummy_128) (nb057_alpha_dummy_129 f) (nb057_wpp_notmem_0388) (nb057_wpp_notmem_0389 f) (TEnvFresh.consFresh (nb057_alpha_dummy_046) (nb057_alpha_dummy_049 f) (nb057_wpp_notmem_0286) (nb057_wpp_notmem_0287 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0180) (nb057_wpp_notmem_0181 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0182) (nb057_wpp_notmem_0183 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0184) (nb057_wpp_notmem_0185 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0186) (nb057_wpp_notmem_0187 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0188) (nb057_wpp_notmem_0189 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0066) (nb057_wpp_notmem_0067 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0068) (nb057_wpp_notmem_0069 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0070) (nb057_wpp_notmem_0071 f a) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))))

noncomputable def nb057_wpp_refl_0023 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)), ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)), ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_136), (nb057_alpha_dummy_137 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0023 f a)

noncomputable def nb057_split_alpha_0016 (f : Var) (a : Var) : TAlphaWff [((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)), ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_136), (nb057_alpha_dummy_137 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_138)) (Class.cv (nb057_alpha_dummy_131))) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_139)) (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_138)) (syn_cnnc)) (syn_cplc (Class.cv (nb057_alpha_dummy_138)) (syn_c1c)) (Class.cv (nb057_alpha_dummy_138)))))) (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_140 f)) (Class.cv (nb057_alpha_dummy_133 f))) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_141 f)) (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_140 f)) (syn_cnnc)) (syn_cplc (Class.cv (nb057_alpha_dummy_140 f)) (syn_c1c)) (Class.cv (nb057_alpha_dummy_140 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0132) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0133 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0132) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0133 f) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_131))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_133 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0136) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0137 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0136) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0137 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)), ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)), ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)), ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)), ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)), ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_136), (nb057_alpha_dummy_137 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_c1c) (nb057_wpp_refl_0021 f a))) (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0015 f a)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)), ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)), ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_136), (nb057_alpha_dummy_137 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_cnnc) (nb057_wpp_refl_0023 f a))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)), ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)), ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_136), (nb057_alpha_dummy_137 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_cnnc) (nb057_wpp_refl_0023 f a))))))))))))

theorem nb057_compact_fv_empty_0122 : (nb057_alpha_dummy_164) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0390 : (nb057_alpha_dummy_164) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_164, fv_syn_c1c] using (nb057_compact_fv_empty_0122)

theorem nb057_compact_fv_empty_0123 (f : Var) : (nb057_alpha_dummy_165 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0391 (f : Var) : (nb057_alpha_dummy_165 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_165, fv_syn_c1c] using (nb057_compact_fv_empty_0123 f)

theorem nb057_compact_fv_empty_0124 : (nb057_alpha_dummy_162) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0392 : (nb057_alpha_dummy_162) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_162, fv_syn_c1c] using (nb057_compact_fv_empty_0124)

theorem nb057_compact_fv_empty_0125 (f : Var) : (nb057_alpha_dummy_163 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0393 (f : Var) : (nb057_alpha_dummy_163 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_163, fv_syn_c1c] using (nb057_compact_fv_empty_0125 f)

theorem nb057_compact_fv_empty_0126 : (nb057_alpha_dummy_160) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0394 : (nb057_alpha_dummy_160) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_160, fv_syn_c1c] using (nb057_compact_fv_empty_0126)

theorem nb057_compact_fv_empty_0127 (f : Var) : (nb057_alpha_dummy_161 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0395 (f : Var) : (nb057_alpha_dummy_161 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_161, fv_syn_c1c] using (nb057_compact_fv_empty_0127 f)

theorem nb057_compact_envfresh_0024 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)), ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)), ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)), ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)), ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)), ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)), ((nb057_alpha_dummy_164), (nb057_alpha_dummy_165 f)), ((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_146) (nb057_alpha_dummy_149 f) (nb057_wpp_notmem_0318) (nb057_wpp_notmem_0319 f) (TEnvFresh.consFresh (nb057_alpha_dummy_145) (nb057_alpha_dummy_148 f) (nb057_wpp_notmem_0320) (nb057_wpp_notmem_0321 f) (TEnvFresh.consFresh (nb057_alpha_dummy_144) (nb057_alpha_dummy_147 f) (nb057_wpp_notmem_0322) (nb057_wpp_notmem_0323 f) (TEnvFresh.consFresh (nb057_alpha_dummy_142) (nb057_alpha_dummy_143 f) (nb057_wpp_notmem_0324) (nb057_wpp_notmem_0325 f) (TEnvFresh.consFresh (nb057_alpha_dummy_138) (nb057_alpha_dummy_140 f) (nb057_wpp_notmem_0326) (nb057_wpp_notmem_0327 f) (TEnvFresh.consFresh (nb057_alpha_dummy_139) (nb057_alpha_dummy_141 f) (nb057_wpp_notmem_0328) (nb057_wpp_notmem_0329 f) (TEnvFresh.consFresh (nb057_alpha_dummy_164) (nb057_alpha_dummy_165 f) (nb057_wpp_notmem_0390) (nb057_wpp_notmem_0391 f) (TEnvFresh.consFresh (nb057_alpha_dummy_162) (nb057_alpha_dummy_163 f) (nb057_wpp_notmem_0392) (nb057_wpp_notmem_0393 f) (TEnvFresh.consFresh (nb057_alpha_dummy_131) (nb057_alpha_dummy_133 f) (nb057_wpp_notmem_0330) (nb057_wpp_notmem_0331 f) (TEnvFresh.consFresh (nb057_alpha_dummy_130) (nb057_alpha_dummy_132 f) (nb057_wpp_notmem_0332) (nb057_wpp_notmem_0333 f) (TEnvFresh.consFresh (nb057_alpha_dummy_160) (nb057_alpha_dummy_161 f) (nb057_wpp_notmem_0394) (nb057_wpp_notmem_0395 f) (TEnvFresh.consFresh (nb057_alpha_dummy_134) (nb057_alpha_dummy_135 f) (nb057_wpp_notmem_0336) (nb057_wpp_notmem_0337 f) (TEnvFresh.consFresh (nb057_alpha_dummy_125) (nb057_alpha_dummy_127 f) (nb057_wpp_notmem_0338) (nb057_wpp_notmem_0339 f) (TEnvFresh.consFresh (nb057_alpha_dummy_124) (nb057_alpha_dummy_126 f) (nb057_wpp_notmem_0340) (nb057_wpp_notmem_0341 f) (TEnvFresh.consFresh (nb057_alpha_dummy_128) (nb057_alpha_dummy_129 f) (nb057_wpp_notmem_0342) (nb057_wpp_notmem_0343 f) (TEnvFresh.consFresh (nb057_alpha_dummy_046) (nb057_alpha_dummy_049 f) (nb057_wpp_notmem_0248) (nb057_wpp_notmem_0249 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0126) (nb057_wpp_notmem_0127 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0128) (nb057_wpp_notmem_0129 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0130) (nb057_wpp_notmem_0131 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0132) (nb057_wpp_notmem_0133 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0134) (nb057_wpp_notmem_0135 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0020) (nb057_wpp_notmem_0021 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0022) (nb057_wpp_notmem_0023 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0024) (nb057_wpp_notmem_0025 f a) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))))))

noncomputable def nb057_wpp_refl_0024 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)), ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)), ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)), ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)), ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)), ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)), ((nb057_alpha_dummy_164), (nb057_alpha_dummy_165 f)), ((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0024 f a)

theorem nb057_wpp_notmem_0396 : (nb057_alpha_dummy_164) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_164, fv_syn_c0] using (nb057_compact_fv_empty_0122)

theorem nb057_wpp_notmem_0397 (f : Var) : (nb057_alpha_dummy_165 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_165, fv_syn_c0] using (nb057_compact_fv_empty_0123 f)

theorem nb057_wpp_notmem_0398 : (nb057_alpha_dummy_162) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_162, fv_syn_c0] using (nb057_compact_fv_empty_0124)

theorem nb057_wpp_notmem_0399 (f : Var) : (nb057_alpha_dummy_163 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_163, fv_syn_c0] using (nb057_compact_fv_empty_0125 f)

theorem nb057_wpp_notmem_0400 : (nb057_alpha_dummy_160) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_160, fv_syn_c0] using (nb057_compact_fv_empty_0126)

theorem nb057_wpp_notmem_0401 (f : Var) : (nb057_alpha_dummy_161 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_161, fv_syn_c0] using (nb057_compact_fv_empty_0127 f)

theorem nb057_compact_envfresh_0025 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)), ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)), ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)), ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)), ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)), ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)), ((nb057_alpha_dummy_164), (nb057_alpha_dummy_165 f)), ((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_146) (nb057_alpha_dummy_149 f) (nb057_wpp_notmem_0344) (nb057_wpp_notmem_0345 f) (TEnvFresh.consFresh (nb057_alpha_dummy_145) (nb057_alpha_dummy_148 f) (nb057_wpp_notmem_0346) (nb057_wpp_notmem_0347 f) (TEnvFresh.consFresh (nb057_alpha_dummy_144) (nb057_alpha_dummy_147 f) (nb057_wpp_notmem_0348) (nb057_wpp_notmem_0349 f) (TEnvFresh.consFresh (nb057_alpha_dummy_142) (nb057_alpha_dummy_143 f) (nb057_wpp_notmem_0350) (nb057_wpp_notmem_0351 f) (TEnvFresh.consFresh (nb057_alpha_dummy_138) (nb057_alpha_dummy_140 f) (nb057_wpp_notmem_0352) (nb057_wpp_notmem_0353 f) (TEnvFresh.consFresh (nb057_alpha_dummy_139) (nb057_alpha_dummy_141 f) (nb057_wpp_notmem_0354) (nb057_wpp_notmem_0355 f) (TEnvFresh.consFresh (nb057_alpha_dummy_164) (nb057_alpha_dummy_165 f) (nb057_wpp_notmem_0396) (nb057_wpp_notmem_0397 f) (TEnvFresh.consFresh (nb057_alpha_dummy_162) (nb057_alpha_dummy_163 f) (nb057_wpp_notmem_0398) (nb057_wpp_notmem_0399 f) (TEnvFresh.consFresh (nb057_alpha_dummy_131) (nb057_alpha_dummy_133 f) (nb057_wpp_notmem_0356) (nb057_wpp_notmem_0357 f) (TEnvFresh.consFresh (nb057_alpha_dummy_130) (nb057_alpha_dummy_132 f) (nb057_wpp_notmem_0358) (nb057_wpp_notmem_0359 f) (TEnvFresh.consFresh (nb057_alpha_dummy_160) (nb057_alpha_dummy_161 f) (nb057_wpp_notmem_0400) (nb057_wpp_notmem_0401 f) (TEnvFresh.consFresh (nb057_alpha_dummy_134) (nb057_alpha_dummy_135 f) (nb057_wpp_notmem_0362) (nb057_wpp_notmem_0363 f) (TEnvFresh.consFresh (nb057_alpha_dummy_125) (nb057_alpha_dummy_127 f) (nb057_wpp_notmem_0364) (nb057_wpp_notmem_0365 f) (TEnvFresh.consFresh (nb057_alpha_dummy_124) (nb057_alpha_dummy_126 f) (nb057_wpp_notmem_0366) (nb057_wpp_notmem_0367 f) (TEnvFresh.consFresh (nb057_alpha_dummy_128) (nb057_alpha_dummy_129 f) (nb057_wpp_notmem_0368) (nb057_wpp_notmem_0369 f) (TEnvFresh.consFresh (nb057_alpha_dummy_046) (nb057_alpha_dummy_049 f) (nb057_wpp_notmem_0270) (nb057_wpp_notmem_0271 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0156) (nb057_wpp_notmem_0157 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0158) (nb057_wpp_notmem_0159 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0160) (nb057_wpp_notmem_0161 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0162) (nb057_wpp_notmem_0163 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0164) (nb057_wpp_notmem_0165 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0046) (nb057_wpp_notmem_0047 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0048) (nb057_wpp_notmem_0049 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0050) (nb057_wpp_notmem_0051 f a) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))))))

noncomputable def nb057_wpp_refl_0025 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)), ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)), ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)), ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)), ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)), ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)), ((nb057_alpha_dummy_164), (nb057_alpha_dummy_165 f)), ((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0025 f a)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
