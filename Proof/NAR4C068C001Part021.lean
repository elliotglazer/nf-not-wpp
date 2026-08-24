import NAR4C068C001Part020

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

theorem nb068_wpp_notmem_0503 (f : Var) : (nb068_alpha_dummy_198 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_198, fv_syn_cnnc] using (nb068_compact_fv_empty_0155 f)

theorem nb068_compact_envfresh_0033 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)), ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)), ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)), ((nb068_alpha_dummy_201), (nb068_alpha_dummy_202 f)), ((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)), ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)), ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)), ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)), ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)), ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)), ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)), ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_179) (nb068_alpha_dummy_180 f) (nb068_wpp_notmem_0472) (nb068_wpp_notmem_0473 f) (TEnvFresh.consFresh (nb068_alpha_dummy_175) (nb068_alpha_dummy_177 f) (nb068_wpp_notmem_0474) (nb068_wpp_notmem_0475 f) (TEnvFresh.consFresh (nb068_alpha_dummy_176) (nb068_alpha_dummy_178 f) (nb068_wpp_notmem_0476) (nb068_wpp_notmem_0477 f) (TEnvFresh.consFresh (nb068_alpha_dummy_201) (nb068_alpha_dummy_202 f) (nb068_wpp_notmem_0498) (nb068_wpp_notmem_0499 f) (TEnvFresh.consFresh (nb068_alpha_dummy_199) (nb068_alpha_dummy_200 f) (nb068_wpp_notmem_0500) (nb068_wpp_notmem_0501 f) (TEnvFresh.consFresh (nb068_alpha_dummy_168) (nb068_alpha_dummy_170 f) (nb068_wpp_notmem_0478) (nb068_wpp_notmem_0479 f) (TEnvFresh.consFresh (nb068_alpha_dummy_167) (nb068_alpha_dummy_169 f) (nb068_wpp_notmem_0480) (nb068_wpp_notmem_0481 f) (TEnvFresh.consFresh (nb068_alpha_dummy_197) (nb068_alpha_dummy_198 f) (nb068_wpp_notmem_0502) (nb068_wpp_notmem_0503 f) (TEnvFresh.consFresh (nb068_alpha_dummy_171) (nb068_alpha_dummy_172 f) (nb068_wpp_notmem_0484) (nb068_wpp_notmem_0485 f) (TEnvFresh.consFresh (nb068_alpha_dummy_126) (nb068_alpha_dummy_128 f) (nb068_wpp_notmem_0392) (nb068_wpp_notmem_0393 f) (TEnvFresh.consFresh (nb068_alpha_dummy_125) (nb068_alpha_dummy_127 f) (nb068_wpp_notmem_0394) (nb068_wpp_notmem_0395 f) (TEnvFresh.consFresh (nb068_alpha_dummy_129) (nb068_alpha_dummy_130 f) (nb068_wpp_notmem_0396) (nb068_wpp_notmem_0397 f) (TEnvFresh.consFresh (nb068_alpha_dummy_047) (nb068_alpha_dummy_050 f) (nb068_wpp_notmem_0294) (nb068_wpp_notmem_0295 f) (TEnvFresh.consFresh (nb068_alpha_dummy_046) (nb068_alpha_dummy_049 f) (nb068_wpp_notmem_0184) (nb068_wpp_notmem_0185 f) (TEnvFresh.consFresh (nb068_alpha_dummy_045) (nb068_alpha_dummy_048 f) (nb068_wpp_notmem_0186) (nb068_wpp_notmem_0187 f) (TEnvFresh.consFresh (nb068_alpha_dummy_051) (nb068_alpha_dummy_052 f) (nb068_wpp_notmem_0188) (nb068_wpp_notmem_0189 f) (TEnvFresh.consFresh (nb068_alpha_dummy_043) (nb068_alpha_dummy_044 f) (nb068_wpp_notmem_0190) (nb068_wpp_notmem_0191 f) (TEnvFresh.consFresh (nb068_alpha_dummy_041) (nb068_alpha_dummy_042 f) (nb068_wpp_notmem_0192) (nb068_wpp_notmem_0193 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0194) (nb068_wpp_notmem_0195 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0066) (nb068_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0068) (nb068_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0070) (nb068_wpp_notmem_0071 x y f) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))))))))

noncomputable def nb068_wpp_refl_0033 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)), ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)), ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)), ((nb068_alpha_dummy_201), (nb068_alpha_dummy_202 f)), ((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)), ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)), ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)), ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)), ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)), ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)), ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)), ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0033 x y f)

noncomputable def nb068_split_alpha_0023 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)), ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)), ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)), ((nb068_alpha_dummy_201), (nb068_alpha_dummy_202 f)), ((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)), ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)), ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)), ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)), ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)), ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)), ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)), ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_179)) (syn_cplc (Class.cv (nb068_alpha_dummy_175)) (syn_c1c))) (Wff.classMem (Class.cv (nb068_alpha_dummy_175)) (syn_cnnc)))) (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_179)) (Class.cv (nb068_alpha_dummy_175))) (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_175)) (syn_cnnc))))) (Wff.imp (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_180 f)) (syn_cplc (Class.cv (nb068_alpha_dummy_177 f)) (syn_c1c))) (Wff.classMem (Class.cv (nb068_alpha_dummy_177 f)) (syn_cnnc)))) (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_180 f)) (Class.cv (nb068_alpha_dummy_177 f))) (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_177 f)) (syn_cnnc))))) :=
  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0174) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0175 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0174) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0175 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_183), (nb068_alpha_dummy_186 f)), ((nb068_alpha_dummy_182), (nb068_alpha_dummy_185 f)), ((nb068_alpha_dummy_181), (nb068_alpha_dummy_184 f)), ((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)), ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)), ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)), ((nb068_alpha_dummy_201), (nb068_alpha_dummy_202 f)), ((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)), ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)), ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)), ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)), ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)), ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)), ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)), ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c1c) (nb068_wpp_refl_0031 x y f))) (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0022 x y f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)), ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)), ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)), ((nb068_alpha_dummy_201), (nb068_alpha_dummy_202 f)), ((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)), ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)), ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)), ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)), ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)), ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)), ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)), ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0033 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)), ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)), ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)), ((nb068_alpha_dummy_201), (nb068_alpha_dummy_202 f)), ((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)), ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)), ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)), ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)), ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)), ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)), ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)), ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0033 x y f))))))))

theorem nb068_wpp_notmem_0504 : (nb068_alpha_dummy_199) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_199, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0152)

theorem nb068_wpp_notmem_0505 (f : Var) : (nb068_alpha_dummy_200 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_200, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0153 f)

theorem nb068_wpp_notmem_0506 : (nb068_alpha_dummy_168) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_168, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0142)

theorem nb068_wpp_notmem_0507 (f : Var) : (nb068_alpha_dummy_170 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_170, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0143 f)

theorem nb068_wpp_notmem_0508 : (nb068_alpha_dummy_167) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_167, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0144)

theorem nb068_wpp_notmem_0509 (f : Var) : (nb068_alpha_dummy_169 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_169, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0145 f)

theorem nb068_wpp_notmem_0510 : (nb068_alpha_dummy_197) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_197, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0154)

theorem nb068_wpp_notmem_0511 (f : Var) : (nb068_alpha_dummy_198 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_198, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0155 f)

theorem nb068_wpp_notmem_0512 : (nb068_alpha_dummy_171) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_171, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0148)

theorem nb068_wpp_notmem_0513 (f : Var) : (nb068_alpha_dummy_172 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_172, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0149 f)

theorem nb068_compact_envfresh_0034 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)), ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)), ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)), ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)), ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)), ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)), ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)), ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_199) (nb068_alpha_dummy_200 f) (nb068_wpp_notmem_0504) (nb068_wpp_notmem_0505 f) (TEnvFresh.consFresh (nb068_alpha_dummy_168) (nb068_alpha_dummy_170 f) (nb068_wpp_notmem_0506) (nb068_wpp_notmem_0507 f) (TEnvFresh.consFresh (nb068_alpha_dummy_167) (nb068_alpha_dummy_169 f) (nb068_wpp_notmem_0508) (nb068_wpp_notmem_0509 f) (TEnvFresh.consFresh (nb068_alpha_dummy_197) (nb068_alpha_dummy_198 f) (nb068_wpp_notmem_0510) (nb068_wpp_notmem_0511 f) (TEnvFresh.consFresh (nb068_alpha_dummy_171) (nb068_alpha_dummy_172 f) (nb068_wpp_notmem_0512) (nb068_wpp_notmem_0513 f) (TEnvFresh.consFresh (nb068_alpha_dummy_126) (nb068_alpha_dummy_128 f) (nb068_wpp_notmem_0426) (nb068_wpp_notmem_0427 f) (TEnvFresh.consFresh (nb068_alpha_dummy_125) (nb068_alpha_dummy_127 f) (nb068_wpp_notmem_0428) (nb068_wpp_notmem_0429 f) (TEnvFresh.consFresh (nb068_alpha_dummy_129) (nb068_alpha_dummy_130 f) (nb068_wpp_notmem_0430) (nb068_wpp_notmem_0431 f) (TEnvFresh.consFresh (nb068_alpha_dummy_047) (nb068_alpha_dummy_050 f) (nb068_wpp_notmem_0324) (nb068_wpp_notmem_0325 f) (TEnvFresh.consFresh (nb068_alpha_dummy_046) (nb068_alpha_dummy_049 f) (nb068_wpp_notmem_0224) (nb068_wpp_notmem_0225 f) (TEnvFresh.consFresh (nb068_alpha_dummy_045) (nb068_alpha_dummy_048 f) (nb068_wpp_notmem_0226) (nb068_wpp_notmem_0227 f) (TEnvFresh.consFresh (nb068_alpha_dummy_051) (nb068_alpha_dummy_052 f) (nb068_wpp_notmem_0228) (nb068_wpp_notmem_0229 f) (TEnvFresh.consFresh (nb068_alpha_dummy_043) (nb068_alpha_dummy_044 f) (nb068_wpp_notmem_0230) (nb068_wpp_notmem_0231 f) (TEnvFresh.consFresh (nb068_alpha_dummy_041) (nb068_alpha_dummy_042 f) (nb068_wpp_notmem_0232) (nb068_wpp_notmem_0233 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0234) (nb068_wpp_notmem_0235 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0100) (nb068_wpp_notmem_0101 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0102) (nb068_wpp_notmem_0103 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0104) (nb068_wpp_notmem_0105 x y f) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))))))))))

noncomputable def nb068_wpp_refl_0034 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)), ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)), ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)), ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)), ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)), ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)), ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)), ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0034 x y f)

noncomputable def nb068_split_alpha_0024 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)), ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)), ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)), ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)), ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)), ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.neg (Wff.all (nb068_alpha_dummy_168) (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_168)) (Class.cv (nb068_alpha_dummy_125))) (Wff.classEq (Class.cv (nb068_alpha_dummy_167)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168))) (syn_csn (syn_c0c)))))))) (Wff.neg (Wff.all (nb068_alpha_dummy_170 f) (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_170 f)) (Class.cv (nb068_alpha_dummy_127 f))) (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))) (syn_csn (syn_c0c)))))))) :=
  (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0196) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0197 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0193) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0195 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_000))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_126))).fv ∪ ((Class.cv (nb068_alpha_dummy_125))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_127 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0170) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0171 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0170) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0171 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0200) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0201 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0198) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0199 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_168))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_170 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb068_split_alpha_0023 x y f))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0170) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0171 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0170) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0171 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0200) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0201 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0198) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0199 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_168))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_170 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb068_split_alpha_0023 x y f))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)), ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)), ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)), ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)), ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)), ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)), ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)), ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_ccompl (syn_csn (syn_c0c))) (nb068_wpp_refl_0034 x y f)))))))))))))))

noncomputable def nb068_split_alpha_0025 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)), ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)), ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.classMem (syn_cop (Class.cv (nb068_alpha_dummy_126)) (Class.cv (nb068_alpha_dummy_125))) (Class.cv (nb068_alpha_dummy_000))) (Wff.classMem (syn_cop (Class.cv (nb068_alpha_dummy_128 f)) (Class.cv (nb068_alpha_dummy_127 f))) (Class.cv f)) :=
  (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0164) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0166 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0164) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0166 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0168) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0169 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0165) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0167 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_126))).fv ∪ ((Class.cv (nb068_alpha_dummy_125))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_127 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0170) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0171 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0170) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0171 f) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (nb068_split_alpha_0021 x y f))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0164) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0166 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0164) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0166 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0168) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0169 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0165) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0167 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_126))).fv ∪ ((Class.cv (nb068_alpha_dummy_125))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_127 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0170) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0171 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0170) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0171 f) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (nb068_split_alpha_0021 x y f))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (nb068_split_alpha_0024 x y f))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (nb068_split_alpha_0024 x y f)))))))))))))) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0212) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0213 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0212) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0213 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0210) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0211 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0206) 2)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0208 f) 2)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0206) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0208 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0206) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0208 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0207) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0209 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0204) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0205 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0202) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0203 f) 0)) (TAlphaVar.here _ _ _))))))))))))

noncomputable def nb068_split_alpha_0026 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)), ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.all (nb068_alpha_dummy_126) (Wff.neg (syn_wa (Wff.classEq (Class.cv (nb068_alpha_dummy_129)) (syn_cop (Class.cv (nb068_alpha_dummy_125)) (Class.cv (nb068_alpha_dummy_126)))) (syn_wbr (Class.cv (nb068_alpha_dummy_126)) (Class.cv (nb068_alpha_dummy_000)) (Class.cv (nb068_alpha_dummy_125)))))) (Wff.all (nb068_alpha_dummy_128 f) (Wff.neg (syn_wa (Wff.classEq (Class.cv (nb068_alpha_dummy_130 f)) (syn_cop (Class.cv (nb068_alpha_dummy_127 f)) (Class.cv (nb068_alpha_dummy_128 f)))) (syn_wbr (Class.cv (nb068_alpha_dummy_128 f)) (Class.cv f) (Class.cv (nb068_alpha_dummy_127 f)))))) :=
  (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0124) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0125 f) 0))) (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0122) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0123 f) 0))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0126) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0128 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0126) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0128 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0130) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0131 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0127) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0129 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_000))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_125))).fv ∪ ((Class.cv (nb068_alpha_dummy_126))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_128 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0132) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0133 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0132) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0133 f) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (nb068_split_alpha_0016 x y f))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0126) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0128 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0126) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0128 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0130) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0131 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0127) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0129 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_000))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_125))).fv ∪ ((Class.cv (nb068_alpha_dummy_126))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_128 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0132) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0133 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0132) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0133 f) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (nb068_split_alpha_0016 x y f))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0019 x y f))))))))))) (TAlphaWff.neg (nb068_split_alpha_0025 x y f))))))

theorem nb068_compact_fv_empty_0156 : (nb068_alpha_dummy_219) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0514 : (nb068_alpha_dummy_219) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_219, fv_syn_c1c] using (nb068_compact_fv_empty_0156)

theorem nb068_compact_fv_empty_0157 (f : Var) : (nb068_alpha_dummy_222 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0515 (f : Var) : (nb068_alpha_dummy_222 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_222, fv_syn_c1c] using (nb068_compact_fv_empty_0157 f)

theorem nb068_compact_fv_empty_0158 : (nb068_alpha_dummy_218) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0516 : (nb068_alpha_dummy_218) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_218, fv_syn_c1c] using (nb068_compact_fv_empty_0158)

theorem nb068_compact_fv_empty_0159 (f : Var) : (nb068_alpha_dummy_221 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0517 (f : Var) : (nb068_alpha_dummy_221 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_221, fv_syn_c1c] using (nb068_compact_fv_empty_0159 f)

theorem nb068_compact_fv_empty_0160 : (nb068_alpha_dummy_217) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0518 : (nb068_alpha_dummy_217) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_217, fv_syn_c1c] using (nb068_compact_fv_empty_0160)

theorem nb068_compact_fv_empty_0161 (f : Var) : (nb068_alpha_dummy_220 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0519 (f : Var) : (nb068_alpha_dummy_220 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_220, fv_syn_c1c] using (nb068_compact_fv_empty_0161 f)

theorem nb068_compact_fv_empty_0162 : (nb068_alpha_dummy_215) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0520 : (nb068_alpha_dummy_215) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_215, fv_syn_c1c] using (nb068_compact_fv_empty_0162)

theorem nb068_compact_fv_empty_0163 (f : Var) : (nb068_alpha_dummy_216 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0521 (f : Var) : (nb068_alpha_dummy_216 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_216, fv_syn_c1c] using (nb068_compact_fv_empty_0163 f)

theorem nb068_compact_fv_empty_0164 : (nb068_alpha_dummy_211) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0522 : (nb068_alpha_dummy_211) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_211, fv_syn_c1c] using (nb068_compact_fv_empty_0164)

theorem nb068_compact_fv_empty_0165 (f : Var) : (nb068_alpha_dummy_213 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0523 (f : Var) : (nb068_alpha_dummy_213 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_213, fv_syn_c1c] using (nb068_compact_fv_empty_0165 f)

theorem nb068_compact_fv_empty_0166 : (nb068_alpha_dummy_212) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0524 : (nb068_alpha_dummy_212) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_212, fv_syn_c1c] using (nb068_compact_fv_empty_0166)

theorem nb068_compact_fv_empty_0167 (f : Var) : (nb068_alpha_dummy_214 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0525 (f : Var) : (nb068_alpha_dummy_214 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_214, fv_syn_c1c] using (nb068_compact_fv_empty_0167 f)

theorem nb068_compact_fv_empty_0168 : (nb068_alpha_dummy_204) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0526 : (nb068_alpha_dummy_204) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_204, fv_syn_c1c] using (nb068_compact_fv_empty_0168)

theorem nb068_compact_fv_empty_0169 (f : Var) : (nb068_alpha_dummy_206 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0527 (f : Var) : (nb068_alpha_dummy_206 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_206, fv_syn_c1c] using (nb068_compact_fv_empty_0169 f)

theorem nb068_compact_fv_empty_0170 : (nb068_alpha_dummy_203) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0528 : (nb068_alpha_dummy_203) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_203, fv_syn_c1c] using (nb068_compact_fv_empty_0170)

theorem nb068_compact_fv_empty_0171 (f : Var) : (nb068_alpha_dummy_205 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0529 (f : Var) : (nb068_alpha_dummy_205 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_205, fv_syn_c1c] using (nb068_compact_fv_empty_0171 f)

theorem nb068_compact_fv_empty_0172 : (nb068_alpha_dummy_209) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0530 : (nb068_alpha_dummy_209) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_209, fv_syn_c1c] using (nb068_compact_fv_empty_0172)

theorem nb068_compact_fv_empty_0173 (f : Var) : (nb068_alpha_dummy_210 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0531 (f : Var) : (nb068_alpha_dummy_210 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_210, fv_syn_c1c] using (nb068_compact_fv_empty_0173 f)

theorem nb068_compact_fv_empty_0174 : (nb068_alpha_dummy_207) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0532 : (nb068_alpha_dummy_207) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_207, fv_syn_c1c] using (nb068_compact_fv_empty_0174)

theorem nb068_compact_fv_empty_0175 (f : Var) : (nb068_alpha_dummy_208 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0533 (f : Var) : (nb068_alpha_dummy_208 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_208, fv_syn_c1c] using (nb068_compact_fv_empty_0175 f)

theorem nb068_compact_envfresh_0035 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_219), (nb068_alpha_dummy_222 f)), ((nb068_alpha_dummy_218), (nb068_alpha_dummy_221 f)), ((nb068_alpha_dummy_217), (nb068_alpha_dummy_220 f)), ((nb068_alpha_dummy_215), (nb068_alpha_dummy_216 f)), ((nb068_alpha_dummy_211), (nb068_alpha_dummy_213 f)), ((nb068_alpha_dummy_212), (nb068_alpha_dummy_214 f)), ((nb068_alpha_dummy_204), (nb068_alpha_dummy_206 f)), ((nb068_alpha_dummy_203), (nb068_alpha_dummy_205 f)), ((nb068_alpha_dummy_209), (nb068_alpha_dummy_210 f)), ((nb068_alpha_dummy_207), (nb068_alpha_dummy_208 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_219) (nb068_alpha_dummy_222 f) (nb068_wpp_notmem_0514) (nb068_wpp_notmem_0515 f) (TEnvFresh.consFresh (nb068_alpha_dummy_218) (nb068_alpha_dummy_221 f) (nb068_wpp_notmem_0516) (nb068_wpp_notmem_0517 f) (TEnvFresh.consFresh (nb068_alpha_dummy_217) (nb068_alpha_dummy_220 f) (nb068_wpp_notmem_0518) (nb068_wpp_notmem_0519 f) (TEnvFresh.consFresh (nb068_alpha_dummy_215) (nb068_alpha_dummy_216 f) (nb068_wpp_notmem_0520) (nb068_wpp_notmem_0521 f) (TEnvFresh.consFresh (nb068_alpha_dummy_211) (nb068_alpha_dummy_213 f) (nb068_wpp_notmem_0522) (nb068_wpp_notmem_0523 f) (TEnvFresh.consFresh (nb068_alpha_dummy_212) (nb068_alpha_dummy_214 f) (nb068_wpp_notmem_0524) (nb068_wpp_notmem_0525 f) (TEnvFresh.consFresh (nb068_alpha_dummy_204) (nb068_alpha_dummy_206 f) (nb068_wpp_notmem_0526) (nb068_wpp_notmem_0527 f) (TEnvFresh.consFresh (nb068_alpha_dummy_203) (nb068_alpha_dummy_205 f) (nb068_wpp_notmem_0528) (nb068_wpp_notmem_0529 f) (TEnvFresh.consFresh (nb068_alpha_dummy_209) (nb068_alpha_dummy_210 f) (nb068_wpp_notmem_0530) (nb068_wpp_notmem_0531 f) (TEnvFresh.consFresh (nb068_alpha_dummy_207) (nb068_alpha_dummy_208 f) (nb068_wpp_notmem_0532) (nb068_wpp_notmem_0533 f) (TEnvFresh.consFresh (nb068_alpha_dummy_047) (nb068_alpha_dummy_050 f) (nb068_wpp_notmem_0256) (nb068_wpp_notmem_0257 f) (TEnvFresh.consFresh (nb068_alpha_dummy_046) (nb068_alpha_dummy_049 f) (nb068_wpp_notmem_0126) (nb068_wpp_notmem_0127 f) (TEnvFresh.consFresh (nb068_alpha_dummy_045) (nb068_alpha_dummy_048 f) (nb068_wpp_notmem_0128) (nb068_wpp_notmem_0129 f) (TEnvFresh.consFresh (nb068_alpha_dummy_051) (nb068_alpha_dummy_052 f) (nb068_wpp_notmem_0130) (nb068_wpp_notmem_0131 f) (TEnvFresh.consFresh (nb068_alpha_dummy_043) (nb068_alpha_dummy_044 f) (nb068_wpp_notmem_0132) (nb068_wpp_notmem_0133 f) (TEnvFresh.consFresh (nb068_alpha_dummy_041) (nb068_alpha_dummy_042 f) (nb068_wpp_notmem_0134) (nb068_wpp_notmem_0135 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0136) (nb068_wpp_notmem_0137 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0020) (nb068_wpp_notmem_0021 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0022) (nb068_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0024) (nb068_wpp_notmem_0025 x y f) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))

noncomputable def nb068_wpp_refl_0035 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_219), (nb068_alpha_dummy_222 f)), ((nb068_alpha_dummy_218), (nb068_alpha_dummy_221 f)), ((nb068_alpha_dummy_217), (nb068_alpha_dummy_220 f)), ((nb068_alpha_dummy_215), (nb068_alpha_dummy_216 f)), ((nb068_alpha_dummy_211), (nb068_alpha_dummy_213 f)), ((nb068_alpha_dummy_212), (nb068_alpha_dummy_214 f)), ((nb068_alpha_dummy_204), (nb068_alpha_dummy_206 f)), ((nb068_alpha_dummy_203), (nb068_alpha_dummy_205 f)), ((nb068_alpha_dummy_209), (nb068_alpha_dummy_210 f)), ((nb068_alpha_dummy_207), (nb068_alpha_dummy_208 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0035 x y f)

theorem nb068_wpp_notmem_0534 : (nb068_alpha_dummy_219) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_219, fv_syn_c0] using (nb068_compact_fv_empty_0156)

theorem nb068_wpp_notmem_0535 (f : Var) : (nb068_alpha_dummy_222 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_222, fv_syn_c0] using (nb068_compact_fv_empty_0157 f)

theorem nb068_wpp_notmem_0536 : (nb068_alpha_dummy_218) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_218, fv_syn_c0] using (nb068_compact_fv_empty_0158)

theorem nb068_wpp_notmem_0537 (f : Var) : (nb068_alpha_dummy_221 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_221, fv_syn_c0] using (nb068_compact_fv_empty_0159 f)

theorem nb068_wpp_notmem_0538 : (nb068_alpha_dummy_217) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_217, fv_syn_c0] using (nb068_compact_fv_empty_0160)

theorem nb068_wpp_notmem_0539 (f : Var) : (nb068_alpha_dummy_220 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_220, fv_syn_c0] using (nb068_compact_fv_empty_0161 f)

theorem nb068_wpp_notmem_0540 : (nb068_alpha_dummy_215) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_215, fv_syn_c0] using (nb068_compact_fv_empty_0162)

theorem nb068_wpp_notmem_0541 (f : Var) : (nb068_alpha_dummy_216 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_216, fv_syn_c0] using (nb068_compact_fv_empty_0163 f)

theorem nb068_wpp_notmem_0542 : (nb068_alpha_dummy_211) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_211, fv_syn_c0] using (nb068_compact_fv_empty_0164)

theorem nb068_wpp_notmem_0543 (f : Var) : (nb068_alpha_dummy_213 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_213, fv_syn_c0] using (nb068_compact_fv_empty_0165 f)

theorem nb068_wpp_notmem_0544 : (nb068_alpha_dummy_212) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_212, fv_syn_c0] using (nb068_compact_fv_empty_0166)

theorem nb068_wpp_notmem_0545 (f : Var) : (nb068_alpha_dummy_214 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_214, fv_syn_c0] using (nb068_compact_fv_empty_0167 f)

theorem nb068_wpp_notmem_0546 : (nb068_alpha_dummy_204) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_204, fv_syn_c0] using (nb068_compact_fv_empty_0168)

theorem nb068_wpp_notmem_0547 (f : Var) : (nb068_alpha_dummy_206 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_206, fv_syn_c0] using (nb068_compact_fv_empty_0169 f)

theorem nb068_wpp_notmem_0548 : (nb068_alpha_dummy_203) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_203, fv_syn_c0] using (nb068_compact_fv_empty_0170)

theorem nb068_wpp_notmem_0549 (f : Var) : (nb068_alpha_dummy_205 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_205, fv_syn_c0] using (nb068_compact_fv_empty_0171 f)

theorem nb068_wpp_notmem_0550 : (nb068_alpha_dummy_209) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_209, fv_syn_c0] using (nb068_compact_fv_empty_0172)

theorem nb068_wpp_notmem_0551 (f : Var) : (nb068_alpha_dummy_210 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_210, fv_syn_c0] using (nb068_compact_fv_empty_0173 f)

theorem nb068_wpp_notmem_0552 : (nb068_alpha_dummy_207) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_207, fv_syn_c0] using (nb068_compact_fv_empty_0174)

theorem nb068_wpp_notmem_0553 (f : Var) : (nb068_alpha_dummy_208 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_208, fv_syn_c0] using (nb068_compact_fv_empty_0175 f)

theorem nb068_compact_envfresh_0036 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_219), (nb068_alpha_dummy_222 f)), ((nb068_alpha_dummy_218), (nb068_alpha_dummy_221 f)), ((nb068_alpha_dummy_217), (nb068_alpha_dummy_220 f)), ((nb068_alpha_dummy_215), (nb068_alpha_dummy_216 f)), ((nb068_alpha_dummy_211), (nb068_alpha_dummy_213 f)), ((nb068_alpha_dummy_212), (nb068_alpha_dummy_214 f)), ((nb068_alpha_dummy_204), (nb068_alpha_dummy_206 f)), ((nb068_alpha_dummy_203), (nb068_alpha_dummy_205 f)), ((nb068_alpha_dummy_209), (nb068_alpha_dummy_210 f)), ((nb068_alpha_dummy_207), (nb068_alpha_dummy_208 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_219) (nb068_alpha_dummy_222 f) (nb068_wpp_notmem_0534) (nb068_wpp_notmem_0535 f) (TEnvFresh.consFresh (nb068_alpha_dummy_218) (nb068_alpha_dummy_221 f) (nb068_wpp_notmem_0536) (nb068_wpp_notmem_0537 f) (TEnvFresh.consFresh (nb068_alpha_dummy_217) (nb068_alpha_dummy_220 f) (nb068_wpp_notmem_0538) (nb068_wpp_notmem_0539 f) (TEnvFresh.consFresh (nb068_alpha_dummy_215) (nb068_alpha_dummy_216 f) (nb068_wpp_notmem_0540) (nb068_wpp_notmem_0541 f) (TEnvFresh.consFresh (nb068_alpha_dummy_211) (nb068_alpha_dummy_213 f) (nb068_wpp_notmem_0542) (nb068_wpp_notmem_0543 f) (TEnvFresh.consFresh (nb068_alpha_dummy_212) (nb068_alpha_dummy_214 f) (nb068_wpp_notmem_0544) (nb068_wpp_notmem_0545 f) (TEnvFresh.consFresh (nb068_alpha_dummy_204) (nb068_alpha_dummy_206 f) (nb068_wpp_notmem_0546) (nb068_wpp_notmem_0547 f) (TEnvFresh.consFresh (nb068_alpha_dummy_203) (nb068_alpha_dummy_205 f) (nb068_wpp_notmem_0548) (nb068_wpp_notmem_0549 f) (TEnvFresh.consFresh (nb068_alpha_dummy_209) (nb068_alpha_dummy_210 f) (nb068_wpp_notmem_0550) (nb068_wpp_notmem_0551 f) (TEnvFresh.consFresh (nb068_alpha_dummy_207) (nb068_alpha_dummy_208 f) (nb068_wpp_notmem_0552) (nb068_wpp_notmem_0553 f) (TEnvFresh.consFresh (nb068_alpha_dummy_047) (nb068_alpha_dummy_050 f) (nb068_wpp_notmem_0278) (nb068_wpp_notmem_0279 f) (TEnvFresh.consFresh (nb068_alpha_dummy_046) (nb068_alpha_dummy_049 f) (nb068_wpp_notmem_0158) (nb068_wpp_notmem_0159 f) (TEnvFresh.consFresh (nb068_alpha_dummy_045) (nb068_alpha_dummy_048 f) (nb068_wpp_notmem_0160) (nb068_wpp_notmem_0161 f) (TEnvFresh.consFresh (nb068_alpha_dummy_051) (nb068_alpha_dummy_052 f) (nb068_wpp_notmem_0162) (nb068_wpp_notmem_0163 f) (TEnvFresh.consFresh (nb068_alpha_dummy_043) (nb068_alpha_dummy_044 f) (nb068_wpp_notmem_0164) (nb068_wpp_notmem_0165 f) (TEnvFresh.consFresh (nb068_alpha_dummy_041) (nb068_alpha_dummy_042 f) (nb068_wpp_notmem_0166) (nb068_wpp_notmem_0167 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0168) (nb068_wpp_notmem_0169 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0046) (nb068_wpp_notmem_0047 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0048) (nb068_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0050) (nb068_wpp_notmem_0051 x y f) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))

noncomputable def nb068_wpp_refl_0036 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_219), (nb068_alpha_dummy_222 f)), ((nb068_alpha_dummy_218), (nb068_alpha_dummy_221 f)), ((nb068_alpha_dummy_217), (nb068_alpha_dummy_220 f)), ((nb068_alpha_dummy_215), (nb068_alpha_dummy_216 f)), ((nb068_alpha_dummy_211), (nb068_alpha_dummy_213 f)), ((nb068_alpha_dummy_212), (nb068_alpha_dummy_214 f)), ((nb068_alpha_dummy_204), (nb068_alpha_dummy_206 f)), ((nb068_alpha_dummy_203), (nb068_alpha_dummy_205 f)), ((nb068_alpha_dummy_209), (nb068_alpha_dummy_210 f)), ((nb068_alpha_dummy_207), (nb068_alpha_dummy_208 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0036 x y f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
