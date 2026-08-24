import NAR4C067C001Part016

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

noncomputable def nb067_split_alpha_0022 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)), ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)), ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)), ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)), ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)), ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)), ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)), ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_183)) (syn_cun (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_187 f)) (Class.cv (nb067_alpha_dummy_188 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_186 f)) (syn_cun (Class.cv (nb067_alpha_dummy_187 f)) (Class.cv (nb067_alpha_dummy_188 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0190) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0191 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0188) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0189 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0194) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0195 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0192) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0193 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0190) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0191 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0188) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0189 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0194) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0195 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0192) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0193 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)), ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)), ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)), ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)), ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)), ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)), ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)), ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_c0) (nb067_wpp_refl_0033 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0198) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0199 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0196) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0197 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0198) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0199 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0196) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0197 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0202) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0203 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0200) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0201 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0202) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0203 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0200) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0201 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb067_wpp_notmem_0510 : (nb067_alpha_dummy_203) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_203, fv_syn_cnnc] using (nb067_compact_fv_empty_0152)

theorem nb067_wpp_notmem_0511 (f : Var) : (nb067_alpha_dummy_204 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_204, fv_syn_cnnc] using (nb067_compact_fv_empty_0153 f)

theorem nb067_wpp_notmem_0512 : (nb067_alpha_dummy_201) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_201, fv_syn_cnnc] using (nb067_compact_fv_empty_0154)

theorem nb067_wpp_notmem_0513 (f : Var) : (nb067_alpha_dummy_202 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_202, fv_syn_cnnc] using (nb067_compact_fv_empty_0155 f)

theorem nb067_wpp_notmem_0514 : (nb067_alpha_dummy_199) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_199, fv_syn_cnnc] using (nb067_compact_fv_empty_0156)

theorem nb067_wpp_notmem_0515 (f : Var) : (nb067_alpha_dummy_200 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_200, fv_syn_cnnc] using (nb067_compact_fv_empty_0157 f)

theorem nb067_compact_envfresh_0034 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)), ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)), ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)), ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)), ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_181) (nb067_alpha_dummy_182 f) (nb067_wpp_notmem_0478) (nb067_wpp_notmem_0479 f) (TEnvFresh.consFresh (nb067_alpha_dummy_177) (nb067_alpha_dummy_179 f) (nb067_wpp_notmem_0480) (nb067_wpp_notmem_0481 f) (TEnvFresh.consFresh (nb067_alpha_dummy_178) (nb067_alpha_dummy_180 f) (nb067_wpp_notmem_0482) (nb067_wpp_notmem_0483 f) (TEnvFresh.consFresh (nb067_alpha_dummy_203) (nb067_alpha_dummy_204 f) (nb067_wpp_notmem_0510) (nb067_wpp_notmem_0511 f) (TEnvFresh.consFresh (nb067_alpha_dummy_201) (nb067_alpha_dummy_202 f) (nb067_wpp_notmem_0512) (nb067_wpp_notmem_0513 f) (TEnvFresh.consFresh (nb067_alpha_dummy_170) (nb067_alpha_dummy_172 f) (nb067_wpp_notmem_0484) (nb067_wpp_notmem_0485 f) (TEnvFresh.consFresh (nb067_alpha_dummy_169) (nb067_alpha_dummy_171 f) (nb067_wpp_notmem_0486) (nb067_wpp_notmem_0487 f) (TEnvFresh.consFresh (nb067_alpha_dummy_199) (nb067_alpha_dummy_200 f) (nb067_wpp_notmem_0514) (nb067_wpp_notmem_0515 f) (TEnvFresh.consFresh (nb067_alpha_dummy_173) (nb067_alpha_dummy_174 f) (nb067_wpp_notmem_0490) (nb067_wpp_notmem_0491 f) (TEnvFresh.consFresh (nb067_alpha_dummy_164) (nb067_alpha_dummy_166 f) (nb067_wpp_notmem_0492) (nb067_wpp_notmem_0493 f) (TEnvFresh.consFresh (nb067_alpha_dummy_163) (nb067_alpha_dummy_165 f) (nb067_wpp_notmem_0494) (nb067_wpp_notmem_0495 f) (TEnvFresh.consFresh (nb067_alpha_dummy_167) (nb067_alpha_dummy_168 f) (nb067_wpp_notmem_0496) (nb067_wpp_notmem_0497 f) (TEnvFresh.consFresh (nb067_alpha_dummy_085) (nb067_alpha_dummy_088 f) (nb067_wpp_notmem_0394) (nb067_wpp_notmem_0395 f) (TEnvFresh.consFresh (nb067_alpha_dummy_084) (nb067_alpha_dummy_087 f) (nb067_wpp_notmem_0284) (nb067_wpp_notmem_0285 f) (TEnvFresh.consFresh (nb067_alpha_dummy_083) (nb067_alpha_dummy_086 f) (nb067_wpp_notmem_0286) (nb067_wpp_notmem_0287 f) (TEnvFresh.consFresh (nb067_alpha_dummy_089) (nb067_alpha_dummy_090 f) (nb067_wpp_notmem_0288) (nb067_wpp_notmem_0289 f) (TEnvFresh.consFresh (nb067_alpha_dummy_081) (nb067_alpha_dummy_082 f) (nb067_wpp_notmem_0290) (nb067_wpp_notmem_0291 f) (TEnvFresh.consFresh (nb067_alpha_dummy_079) (nb067_alpha_dummy_080 f) (nb067_wpp_notmem_0292) (nb067_wpp_notmem_0293 f) (TEnvFresh.consFresh (nb067_alpha_dummy_000) f (nb067_wpp_notmem_0294) (nb067_wpp_notmem_0295 f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0094) (nb067_wpp_notmem_0095 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0096) (nb067_wpp_notmem_0097 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0098) (nb067_wpp_notmem_0099 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0100) (nb067_wpp_notmem_0101 x y f) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))))))))

noncomputable def nb067_wpp_refl_0034 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)), ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)), ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)), ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)), ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0034 x y f)

noncomputable def nb067_split_alpha_0023 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)), ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)), ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)), ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)), ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (Wff.imp (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_181)) (syn_cplc (Class.cv (nb067_alpha_dummy_177)) (syn_c1c))) (Wff.classMem (Class.cv (nb067_alpha_dummy_177)) (syn_cnnc)))) (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_181)) (Class.cv (nb067_alpha_dummy_177))) (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_177)) (syn_cnnc))))) (Wff.imp (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_182 f)) (syn_cplc (Class.cv (nb067_alpha_dummy_179 f)) (syn_c1c))) (Wff.classMem (Class.cv (nb067_alpha_dummy_179 f)) (syn_cnnc)))) (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_182 f)) (Class.cv (nb067_alpha_dummy_179 f))) (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_179 f)) (syn_cnnc))))) :=
  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0186) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0187 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0186) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0187 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)), ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)), ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)), ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)), ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)), ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)), ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)), ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_c1c) (nb067_wpp_refl_0032 x y f))) (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0022 x y f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)), ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)), ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)), ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)), ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_cnnc) (nb067_wpp_refl_0034 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)), ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)), ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)), ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)), ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_cnnc) (nb067_wpp_refl_0034 x y f))))))))

theorem nb067_wpp_notmem_0516 : (nb067_alpha_dummy_201) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_201, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0154)

theorem nb067_wpp_notmem_0517 (f : Var) : (nb067_alpha_dummy_202 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_202, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0155 f)

theorem nb067_wpp_notmem_0518 : (nb067_alpha_dummy_170) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_170, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0138)

theorem nb067_wpp_notmem_0519 (f : Var) : (nb067_alpha_dummy_172 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_172, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0139 f)

theorem nb067_wpp_notmem_0520 : (nb067_alpha_dummy_169) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_169, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0140)

theorem nb067_wpp_notmem_0521 (f : Var) : (nb067_alpha_dummy_171 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_171, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0141 f)

theorem nb067_wpp_notmem_0522 : (nb067_alpha_dummy_199) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_199, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0156)

theorem nb067_wpp_notmem_0523 (f : Var) : (nb067_alpha_dummy_200 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_200, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0157 f)

theorem nb067_wpp_notmem_0524 : (nb067_alpha_dummy_173) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_173, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0144)

theorem nb067_wpp_notmem_0525 (f : Var) : (nb067_alpha_dummy_174 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_174, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0145 f)

theorem nb067_wpp_notmem_0526 : (nb067_alpha_dummy_164) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_164, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0146)

theorem nb067_wpp_notmem_0527 (f : Var) : (nb067_alpha_dummy_166 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_166, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0147 f)

theorem nb067_wpp_notmem_0528 : (nb067_alpha_dummy_163) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_163, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0148)

theorem nb067_wpp_notmem_0529 (f : Var) : (nb067_alpha_dummy_165 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_165, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0149 f)

theorem nb067_wpp_notmem_0530 : (nb067_alpha_dummy_167) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_167, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0150)

theorem nb067_wpp_notmem_0531 (f : Var) : (nb067_alpha_dummy_168 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_168, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0151 f)

theorem nb067_compact_envfresh_0035 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_201) (nb067_alpha_dummy_202 f) (nb067_wpp_notmem_0516) (nb067_wpp_notmem_0517 f) (TEnvFresh.consFresh (nb067_alpha_dummy_170) (nb067_alpha_dummy_172 f) (nb067_wpp_notmem_0518) (nb067_wpp_notmem_0519 f) (TEnvFresh.consFresh (nb067_alpha_dummy_169) (nb067_alpha_dummy_171 f) (nb067_wpp_notmem_0520) (nb067_wpp_notmem_0521 f) (TEnvFresh.consFresh (nb067_alpha_dummy_199) (nb067_alpha_dummy_200 f) (nb067_wpp_notmem_0522) (nb067_wpp_notmem_0523 f) (TEnvFresh.consFresh (nb067_alpha_dummy_173) (nb067_alpha_dummy_174 f) (nb067_wpp_notmem_0524) (nb067_wpp_notmem_0525 f) (TEnvFresh.consFresh (nb067_alpha_dummy_164) (nb067_alpha_dummy_166 f) (nb067_wpp_notmem_0526) (nb067_wpp_notmem_0527 f) (TEnvFresh.consFresh (nb067_alpha_dummy_163) (nb067_alpha_dummy_165 f) (nb067_wpp_notmem_0528) (nb067_wpp_notmem_0529 f) (TEnvFresh.consFresh (nb067_alpha_dummy_167) (nb067_alpha_dummy_168 f) (nb067_wpp_notmem_0530) (nb067_wpp_notmem_0531 f) (TEnvFresh.consFresh (nb067_alpha_dummy_085) (nb067_alpha_dummy_088 f) (nb067_wpp_notmem_0424) (nb067_wpp_notmem_0425 f) (TEnvFresh.consFresh (nb067_alpha_dummy_084) (nb067_alpha_dummy_087 f) (nb067_wpp_notmem_0324) (nb067_wpp_notmem_0325 f) (TEnvFresh.consFresh (nb067_alpha_dummy_083) (nb067_alpha_dummy_086 f) (nb067_wpp_notmem_0326) (nb067_wpp_notmem_0327 f) (TEnvFresh.consFresh (nb067_alpha_dummy_089) (nb067_alpha_dummy_090 f) (nb067_wpp_notmem_0328) (nb067_wpp_notmem_0329 f) (TEnvFresh.consFresh (nb067_alpha_dummy_081) (nb067_alpha_dummy_082 f) (nb067_wpp_notmem_0330) (nb067_wpp_notmem_0331 f) (TEnvFresh.consFresh (nb067_alpha_dummy_079) (nb067_alpha_dummy_080 f) (nb067_wpp_notmem_0332) (nb067_wpp_notmem_0333 f) (TEnvFresh.consFresh (nb067_alpha_dummy_000) f (nb067_wpp_notmem_0334) (nb067_wpp_notmem_0335 f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0138) (nb067_wpp_notmem_0139 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0140) (nb067_wpp_notmem_0141 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0142) (nb067_wpp_notmem_0143 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0144) (nb067_wpp_notmem_0145 x y f) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))))))))

noncomputable def nb067_wpp_refl_0035 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0035 x y f)

noncomputable def nb067_split_alpha_0024 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_199)) (Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_199)) (Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170))) (syn_csn (syn_c0c))))))))) (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_200 f)) (Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_200 f)) (Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))) (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0206 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0206 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0208) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0209 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0205) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0207 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_163))).fv ∪ ((Class.cv (nb067_alpha_dummy_164))).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_166 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0182) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0183 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0182) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0183 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0212) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0213 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0210) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0211 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_170))).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_172 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb067_split_alpha_0023 x y f))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0182) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0183 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0182) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0183 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0212) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0213 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0210) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0211 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_170))).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_172 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb067_split_alpha_0023 x y f))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_ccompl (syn_csn (syn_c0c))) (nb067_wpp_refl_0035 x y f))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0206 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0206 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0208) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0209 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0205) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0207 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_163))).fv ∪ ((Class.cv (nb067_alpha_dummy_164))).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_166 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0182) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0183 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0182) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0183 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0212) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0213 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0210) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0211 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_170))).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_172 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb067_split_alpha_0023 x y f))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0182) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0183 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0182) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0183 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0212) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0213 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0210) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0211 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_170))).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_172 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb067_split_alpha_0023 x y f))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_ccompl (syn_csn (syn_c0c))) (nb067_wpp_refl_0035 x y f)))))))))))))))))))

theorem nb067_compact_fv_empty_0158 : (nb067_alpha_dummy_221) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0532 : (nb067_alpha_dummy_221) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_221, fv_syn_c1c] using (nb067_compact_fv_empty_0158)

theorem nb067_compact_fv_empty_0159 (f : Var) : (nb067_alpha_dummy_224 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0533 (f : Var) : (nb067_alpha_dummy_224 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_224, fv_syn_c1c] using (nb067_compact_fv_empty_0159 f)

theorem nb067_compact_fv_empty_0160 : (nb067_alpha_dummy_220) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0534 : (nb067_alpha_dummy_220) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_220, fv_syn_c1c] using (nb067_compact_fv_empty_0160)

theorem nb067_compact_fv_empty_0161 (f : Var) : (nb067_alpha_dummy_223 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0535 (f : Var) : (nb067_alpha_dummy_223 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_223, fv_syn_c1c] using (nb067_compact_fv_empty_0161 f)

theorem nb067_compact_fv_empty_0162 : (nb067_alpha_dummy_219) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0536 : (nb067_alpha_dummy_219) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_219, fv_syn_c1c] using (nb067_compact_fv_empty_0162)

theorem nb067_compact_fv_empty_0163 (f : Var) : (nb067_alpha_dummy_222 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0537 (f : Var) : (nb067_alpha_dummy_222 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_222, fv_syn_c1c] using (nb067_compact_fv_empty_0163 f)

theorem nb067_compact_fv_empty_0164 : (nb067_alpha_dummy_217) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0538 : (nb067_alpha_dummy_217) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_217, fv_syn_c1c] using (nb067_compact_fv_empty_0164)

theorem nb067_compact_fv_empty_0165 (f : Var) : (nb067_alpha_dummy_218 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0539 (f : Var) : (nb067_alpha_dummy_218 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_218, fv_syn_c1c] using (nb067_compact_fv_empty_0165 f)

theorem nb067_compact_fv_empty_0166 : (nb067_alpha_dummy_213) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0540 : (nb067_alpha_dummy_213) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_213, fv_syn_c1c] using (nb067_compact_fv_empty_0166)

theorem nb067_compact_fv_empty_0167 (f : Var) : (nb067_alpha_dummy_215 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0541 (f : Var) : (nb067_alpha_dummy_215 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_215, fv_syn_c1c] using (nb067_compact_fv_empty_0167 f)

theorem nb067_compact_fv_empty_0168 : (nb067_alpha_dummy_214) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0542 : (nb067_alpha_dummy_214) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_214, fv_syn_c1c] using (nb067_compact_fv_empty_0168)

theorem nb067_compact_fv_empty_0169 (f : Var) : (nb067_alpha_dummy_216 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0543 (f : Var) : (nb067_alpha_dummy_216 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_216, fv_syn_c1c] using (nb067_compact_fv_empty_0169 f)

theorem nb067_compact_fv_empty_0170 : (nb067_alpha_dummy_206) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0544 : (nb067_alpha_dummy_206) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_206, fv_syn_c1c] using (nb067_compact_fv_empty_0170)

theorem nb067_compact_fv_empty_0171 (f : Var) : (nb067_alpha_dummy_208 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0545 (f : Var) : (nb067_alpha_dummy_208 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_208, fv_syn_c1c] using (nb067_compact_fv_empty_0171 f)

theorem nb067_compact_fv_empty_0172 : (nb067_alpha_dummy_205) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0546 : (nb067_alpha_dummy_205) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_205, fv_syn_c1c] using (nb067_compact_fv_empty_0172)

theorem nb067_compact_fv_empty_0173 (f : Var) : (nb067_alpha_dummy_207 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0547 (f : Var) : (nb067_alpha_dummy_207 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_207, fv_syn_c1c] using (nb067_compact_fv_empty_0173 f)

theorem nb067_compact_fv_empty_0174 : (nb067_alpha_dummy_211) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0548 : (nb067_alpha_dummy_211) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_211, fv_syn_c1c] using (nb067_compact_fv_empty_0174)

theorem nb067_compact_fv_empty_0175 (f : Var) : (nb067_alpha_dummy_212 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0549 (f : Var) : (nb067_alpha_dummy_212 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_212, fv_syn_c1c] using (nb067_compact_fv_empty_0175 f)

theorem nb067_compact_fv_empty_0176 : (nb067_alpha_dummy_209) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0550 : (nb067_alpha_dummy_209) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_209, fv_syn_c1c] using (nb067_compact_fv_empty_0176)

theorem nb067_compact_fv_empty_0177 (f : Var) : (nb067_alpha_dummy_210 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0551 (f : Var) : (nb067_alpha_dummy_210 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_210, fv_syn_c1c] using (nb067_compact_fv_empty_0177 f)

theorem nb067_compact_envfresh_0036 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_221), (nb067_alpha_dummy_224 f)), ((nb067_alpha_dummy_220), (nb067_alpha_dummy_223 f)), ((nb067_alpha_dummy_219), (nb067_alpha_dummy_222 f)), ((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)), ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)), ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)), ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)), ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)), ((nb067_alpha_dummy_211), (nb067_alpha_dummy_212 f)), ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_221) (nb067_alpha_dummy_224 f) (nb067_wpp_notmem_0532) (nb067_wpp_notmem_0533 f) (TEnvFresh.consFresh (nb067_alpha_dummy_220) (nb067_alpha_dummy_223 f) (nb067_wpp_notmem_0534) (nb067_wpp_notmem_0535 f) (TEnvFresh.consFresh (nb067_alpha_dummy_219) (nb067_alpha_dummy_222 f) (nb067_wpp_notmem_0536) (nb067_wpp_notmem_0537 f) (TEnvFresh.consFresh (nb067_alpha_dummy_217) (nb067_alpha_dummy_218 f) (nb067_wpp_notmem_0538) (nb067_wpp_notmem_0539 f) (TEnvFresh.consFresh (nb067_alpha_dummy_213) (nb067_alpha_dummy_215 f) (nb067_wpp_notmem_0540) (nb067_wpp_notmem_0541 f) (TEnvFresh.consFresh (nb067_alpha_dummy_214) (nb067_alpha_dummy_216 f) (nb067_wpp_notmem_0542) (nb067_wpp_notmem_0543 f) (TEnvFresh.consFresh (nb067_alpha_dummy_206) (nb067_alpha_dummy_208 f) (nb067_wpp_notmem_0544) (nb067_wpp_notmem_0545 f) (TEnvFresh.consFresh (nb067_alpha_dummy_205) (nb067_alpha_dummy_207 f) (nb067_wpp_notmem_0546) (nb067_wpp_notmem_0547 f) (TEnvFresh.consFresh (nb067_alpha_dummy_211) (nb067_alpha_dummy_212 f) (nb067_wpp_notmem_0548) (nb067_wpp_notmem_0549 f) (TEnvFresh.consFresh (nb067_alpha_dummy_209) (nb067_alpha_dummy_210 f) (nb067_wpp_notmem_0550) (nb067_wpp_notmem_0551 f) (TEnvFresh.consFresh (nb067_alpha_dummy_164) (nb067_alpha_dummy_166 f) (nb067_wpp_notmem_0446) (nb067_wpp_notmem_0447 f) (TEnvFresh.consFresh (nb067_alpha_dummy_163) (nb067_alpha_dummy_165 f) (nb067_wpp_notmem_0448) (nb067_wpp_notmem_0449 f) (TEnvFresh.consFresh (nb067_alpha_dummy_167) (nb067_alpha_dummy_168 f) (nb067_wpp_notmem_0450) (nb067_wpp_notmem_0451 f) (TEnvFresh.consFresh (nb067_alpha_dummy_085) (nb067_alpha_dummy_088 f) (nb067_wpp_notmem_0356) (nb067_wpp_notmem_0357 f) (TEnvFresh.consFresh (nb067_alpha_dummy_084) (nb067_alpha_dummy_087 f) (nb067_wpp_notmem_0226) (nb067_wpp_notmem_0227 f) (TEnvFresh.consFresh (nb067_alpha_dummy_083) (nb067_alpha_dummy_086 f) (nb067_wpp_notmem_0228) (nb067_wpp_notmem_0229 f) (TEnvFresh.consFresh (nb067_alpha_dummy_089) (nb067_alpha_dummy_090 f) (nb067_wpp_notmem_0230) (nb067_wpp_notmem_0231 f) (TEnvFresh.consFresh (nb067_alpha_dummy_081) (nb067_alpha_dummy_082 f) (nb067_wpp_notmem_0232) (nb067_wpp_notmem_0233 f) (TEnvFresh.consFresh (nb067_alpha_dummy_079) (nb067_alpha_dummy_080 f) (nb067_wpp_notmem_0234) (nb067_wpp_notmem_0235 f) (TEnvFresh.consFresh (nb067_alpha_dummy_000) f (nb067_wpp_notmem_0236) (nb067_wpp_notmem_0237 f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0028) (nb067_wpp_notmem_0029 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0030) (nb067_wpp_notmem_0031 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0032) (nb067_wpp_notmem_0033 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0034) (nb067_wpp_notmem_0035 x y f) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))))))

noncomputable def nb067_wpp_refl_0036 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_221), (nb067_alpha_dummy_224 f)), ((nb067_alpha_dummy_220), (nb067_alpha_dummy_223 f)), ((nb067_alpha_dummy_219), (nb067_alpha_dummy_222 f)), ((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)), ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)), ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)), ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)), ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)), ((nb067_alpha_dummy_211), (nb067_alpha_dummy_212 f)), ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0036 x y f)

theorem nb067_wpp_notmem_0552 : (nb067_alpha_dummy_221) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_221, fv_syn_c0] using (nb067_compact_fv_empty_0158)

theorem nb067_wpp_notmem_0553 (f : Var) : (nb067_alpha_dummy_224 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_224, fv_syn_c0] using (nb067_compact_fv_empty_0159 f)

theorem nb067_wpp_notmem_0554 : (nb067_alpha_dummy_220) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_220, fv_syn_c0] using (nb067_compact_fv_empty_0160)

theorem nb067_wpp_notmem_0555 (f : Var) : (nb067_alpha_dummy_223 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_223, fv_syn_c0] using (nb067_compact_fv_empty_0161 f)

theorem nb067_wpp_notmem_0556 : (nb067_alpha_dummy_219) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_219, fv_syn_c0] using (nb067_compact_fv_empty_0162)

theorem nb067_wpp_notmem_0557 (f : Var) : (nb067_alpha_dummy_222 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_222, fv_syn_c0] using (nb067_compact_fv_empty_0163 f)

theorem nb067_wpp_notmem_0558 : (nb067_alpha_dummy_217) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_217, fv_syn_c0] using (nb067_compact_fv_empty_0164)

theorem nb067_wpp_notmem_0559 (f : Var) : (nb067_alpha_dummy_218 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_218, fv_syn_c0] using (nb067_compact_fv_empty_0165 f)

theorem nb067_wpp_notmem_0560 : (nb067_alpha_dummy_213) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_213, fv_syn_c0] using (nb067_compact_fv_empty_0166)

theorem nb067_wpp_notmem_0561 (f : Var) : (nb067_alpha_dummy_215 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_215, fv_syn_c0] using (nb067_compact_fv_empty_0167 f)

theorem nb067_wpp_notmem_0562 : (nb067_alpha_dummy_214) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_214, fv_syn_c0] using (nb067_compact_fv_empty_0168)

theorem nb067_wpp_notmem_0563 (f : Var) : (nb067_alpha_dummy_216 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_216, fv_syn_c0] using (nb067_compact_fv_empty_0169 f)

theorem nb067_wpp_notmem_0564 : (nb067_alpha_dummy_206) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_206, fv_syn_c0] using (nb067_compact_fv_empty_0170)

theorem nb067_wpp_notmem_0565 (f : Var) : (nb067_alpha_dummy_208 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_208, fv_syn_c0] using (nb067_compact_fv_empty_0171 f)

theorem nb067_wpp_notmem_0566 : (nb067_alpha_dummy_205) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_205, fv_syn_c0] using (nb067_compact_fv_empty_0172)

theorem nb067_wpp_notmem_0567 (f : Var) : (nb067_alpha_dummy_207 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_207, fv_syn_c0] using (nb067_compact_fv_empty_0173 f)

theorem nb067_wpp_notmem_0568 : (nb067_alpha_dummy_211) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_211, fv_syn_c0] using (nb067_compact_fv_empty_0174)

theorem nb067_wpp_notmem_0569 (f : Var) : (nb067_alpha_dummy_212 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_212, fv_syn_c0] using (nb067_compact_fv_empty_0175 f)

theorem nb067_wpp_notmem_0570 : (nb067_alpha_dummy_209) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_209, fv_syn_c0] using (nb067_compact_fv_empty_0176)

theorem nb067_wpp_notmem_0571 (f : Var) : (nb067_alpha_dummy_210 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_210, fv_syn_c0] using (nb067_compact_fv_empty_0177 f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
