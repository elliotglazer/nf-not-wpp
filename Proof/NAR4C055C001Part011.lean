import NAR4C055C001Part010

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

noncomputable def nb055_split_alpha_0017 (x : Var) (y : Var) : TAlphaWff [((nb055_alpha_dummy_134), (nb055_alpha_dummy_137 x y)), ((nb055_alpha_dummy_133), (nb055_alpha_dummy_136 x y)), ((nb055_alpha_dummy_132), (nb055_alpha_dummy_135 x y)), ((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)), ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)), ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)), ((nb055_alpha_dummy_152), (nb055_alpha_dummy_153 x y)), ((nb055_alpha_dummy_150), (nb055_alpha_dummy_151 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb055_alpha_dummy_133)) (Class.cv (nb055_alpha_dummy_134))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_132)) (syn_cun (Class.cv (nb055_alpha_dummy_133)) (Class.cv (nb055_alpha_dummy_134)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb055_alpha_dummy_136 x y)) (Class.cv (nb055_alpha_dummy_137 x y))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_135 x y)) (syn_cun (Class.cv (nb055_alpha_dummy_136 x y)) (Class.cv (nb055_alpha_dummy_137 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0148) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0149 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0147 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0152) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0153 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0150) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0151 x y) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0148) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0149 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0147 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0152) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0153 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0150) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0151 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_134), (nb055_alpha_dummy_137 x y)), ((nb055_alpha_dummy_133), (nb055_alpha_dummy_136 x y)), ((nb055_alpha_dummy_132), (nb055_alpha_dummy_135 x y)), ((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)), ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)), ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)), ((nb055_alpha_dummy_152), (nb055_alpha_dummy_153 x y)), ((nb055_alpha_dummy_150), (nb055_alpha_dummy_151 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_c0) (nb055_wpp_refl_0026 x y))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0156) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0157 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0154) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0155 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0156) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0157 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0154) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0155 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0160) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0161 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0158) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0159 x y) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0160) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0161 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0158) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0159 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb055_wpp_notmem_0368 : (nb055_alpha_dummy_152) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_152, fv_syn_cnnc] using (nb055_compact_fv_empty_0110)

theorem nb055_wpp_notmem_0369 (x : Var) (y : Var) : (nb055_alpha_dummy_153 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_153, fv_syn_cnnc] using (nb055_compact_fv_empty_0111 x y)

theorem nb055_wpp_notmem_0370 : (nb055_alpha_dummy_150) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_150, fv_syn_cnnc] using (nb055_compact_fv_empty_0112)

theorem nb055_wpp_notmem_0371 (x : Var) (y : Var) : (nb055_alpha_dummy_151 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_151, fv_syn_cnnc] using (nb055_compact_fv_empty_0113 x y)

theorem nb055_wpp_notmem_0372 : (nb055_alpha_dummy_148) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_148, fv_syn_cnnc] using (nb055_compact_fv_empty_0114)

theorem nb055_wpp_notmem_0373 (x : Var) (y : Var) : (nb055_alpha_dummy_149 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_149, fv_syn_cnnc] using (nb055_compact_fv_empty_0115 x y)

theorem nb055_compact_envfresh_0027 (x : Var) (y : Var) : TEnvFresh [((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)), ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)), ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)), ((nb055_alpha_dummy_152), (nb055_alpha_dummy_153 x y)), ((nb055_alpha_dummy_150), (nb055_alpha_dummy_151 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb055_alpha_dummy_130) (nb055_alpha_dummy_131 x y) (nb055_wpp_notmem_0340) (nb055_wpp_notmem_0341 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_126) (nb055_alpha_dummy_128 x y) (nb055_wpp_notmem_0342) (nb055_wpp_notmem_0343 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_127) (nb055_alpha_dummy_129 x y) (nb055_wpp_notmem_0344) (nb055_wpp_notmem_0345 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_152) (nb055_alpha_dummy_153 x y) (nb055_wpp_notmem_0368) (nb055_wpp_notmem_0369 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_150) (nb055_alpha_dummy_151 x y) (nb055_wpp_notmem_0370) (nb055_wpp_notmem_0371 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_119) (nb055_alpha_dummy_121 x y) (nb055_wpp_notmem_0346) (nb055_wpp_notmem_0347 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_118) (nb055_alpha_dummy_120 x y) (nb055_wpp_notmem_0348) (nb055_wpp_notmem_0349 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_148) (nb055_alpha_dummy_149 x y) (nb055_wpp_notmem_0372) (nb055_wpp_notmem_0373 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_122) (nb055_alpha_dummy_123 x y) (nb055_wpp_notmem_0352) (nb055_wpp_notmem_0353 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_078) (nb055_alpha_dummy_079 x y) (nb055_wpp_notmem_0354) (nb055_wpp_notmem_0355 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_015) (nb055_alpha_dummy_017 x y) (nb055_wpp_notmem_0078) (nb055_wpp_notmem_0079 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_014) (nb055_alpha_dummy_016 x y) (nb055_wpp_notmem_0080) (nb055_wpp_notmem_0081 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_080) (nb055_alpha_dummy_081 x y) (nb055_wpp_notmem_0264) (nb055_wpp_notmem_0265 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_002) (nb055_alpha_dummy_003 x y) (nb055_wpp_notmem_0094) (nb055_wpp_notmem_0095 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_001) y (nb055_wpp_notmem_0096) (nb055_wpp_notmem_0097 y) (TEnvFresh.consFresh (nb055_alpha_dummy_000) x (nb055_wpp_notmem_0098) (nb055_wpp_notmem_0099 x) (TEnvFresh.consFresh (nb055_alpha_dummy_004) (nb055_alpha_dummy_005 x y) (nb055_wpp_notmem_0100) (nb055_wpp_notmem_0101 x y) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))

noncomputable def nb055_wpp_refl_0027 (x : Var) (y : Var) : TReflOn [((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)), ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)), ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)), ((nb055_alpha_dummy_152), (nb055_alpha_dummy_153 x y)), ((nb055_alpha_dummy_150), (nb055_alpha_dummy_151 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb055_compact_envfresh_0027 x y)

noncomputable def nb055_split_alpha_0018 (x : Var) (y : Var) : TAlphaWff [((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)), ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)), ((nb055_alpha_dummy_152), (nb055_alpha_dummy_153 x y)), ((nb055_alpha_dummy_150), (nb055_alpha_dummy_151 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_126)) (Class.cv (nb055_alpha_dummy_119))) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_127)) (syn_cif (Wff.classMem (Class.cv (nb055_alpha_dummy_126)) (syn_cnnc)) (syn_cplc (Class.cv (nb055_alpha_dummy_126)) (syn_c1c)) (Class.cv (nb055_alpha_dummy_126)))))) (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_128 x y)) (Class.cv (nb055_alpha_dummy_121 x y))) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_129 x y)) (syn_cif (Wff.classMem (Class.cv (nb055_alpha_dummy_128 x y)) (syn_cnnc)) (syn_cplc (Class.cv (nb055_alpha_dummy_128 x y)) (syn_c1c)) (Class.cv (nb055_alpha_dummy_128 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0140) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0141 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0140) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0141 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0170) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0171 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0168) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0169 x y) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_119))).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_121 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0144) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0145 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0144) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0145 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0142) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0143 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_134), (nb055_alpha_dummy_137 x y)), ((nb055_alpha_dummy_133), (nb055_alpha_dummy_136 x y)), ((nb055_alpha_dummy_132), (nb055_alpha_dummy_135 x y)), ((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)), ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)), ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)), ((nb055_alpha_dummy_152), (nb055_alpha_dummy_153 x y)), ((nb055_alpha_dummy_150), (nb055_alpha_dummy_151 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_c1c) (nb055_wpp_refl_0025 x y))) (TAlphaWff.neg (TAlphaWff.neg (nb055_split_alpha_0017 x y)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0142) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0143 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)), ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)), ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)), ((nb055_alpha_dummy_152), (nb055_alpha_dummy_153 x y)), ((nb055_alpha_dummy_150), (nb055_alpha_dummy_151 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_cnnc) (nb055_wpp_refl_0027 x y))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0142) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0143 x y) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0142) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0143 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)), ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)), ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)), ((nb055_alpha_dummy_152), (nb055_alpha_dummy_153 x y)), ((nb055_alpha_dummy_150), (nb055_alpha_dummy_151 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_cnnc) (nb055_wpp_refl_0027 x y))))))))))))

theorem nb055_wpp_notmem_0374 : (nb055_alpha_dummy_150) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_150, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0112)

theorem nb055_wpp_notmem_0375 (x : Var) (y : Var) : (nb055_alpha_dummy_151 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_151, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0113 x y)

theorem nb055_wpp_notmem_0376 : (nb055_alpha_dummy_119) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_119, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0100)

theorem nb055_wpp_notmem_0377 (x : Var) (y : Var) : (nb055_alpha_dummy_121 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_121, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0101 x y)

theorem nb055_wpp_notmem_0378 : (nb055_alpha_dummy_118) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_118, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0102)

theorem nb055_wpp_notmem_0379 (x : Var) (y : Var) : (nb055_alpha_dummy_120 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_120, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0103 x y)

theorem nb055_wpp_notmem_0380 : (nb055_alpha_dummy_148) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_148, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0114)

theorem nb055_wpp_notmem_0381 (x : Var) (y : Var) : (nb055_alpha_dummy_149 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_149, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0115 x y)

theorem nb055_wpp_notmem_0382 : (nb055_alpha_dummy_122) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_122, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0106)

theorem nb055_wpp_notmem_0383 (x : Var) (y : Var) : (nb055_alpha_dummy_123 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_123, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0107 x y)

theorem nb055_wpp_notmem_0384 : (nb055_alpha_dummy_078) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_078, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0108)

theorem nb055_wpp_notmem_0385 (x : Var) (y : Var) : (nb055_alpha_dummy_079 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_079, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0109 x y)

theorem nb055_compact_envfresh_0028 (x : Var) (y : Var) : TEnvFresh [((nb055_alpha_dummy_150), (nb055_alpha_dummy_151 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb055_alpha_dummy_150) (nb055_alpha_dummy_151 x y) (nb055_wpp_notmem_0374) (nb055_wpp_notmem_0375 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_119) (nb055_alpha_dummy_121 x y) (nb055_wpp_notmem_0376) (nb055_wpp_notmem_0377 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_118) (nb055_alpha_dummy_120 x y) (nb055_wpp_notmem_0378) (nb055_wpp_notmem_0379 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_148) (nb055_alpha_dummy_149 x y) (nb055_wpp_notmem_0380) (nb055_wpp_notmem_0381 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_122) (nb055_alpha_dummy_123 x y) (nb055_wpp_notmem_0382) (nb055_wpp_notmem_0383 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_078) (nb055_alpha_dummy_079 x y) (nb055_wpp_notmem_0384) (nb055_wpp_notmem_0385 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_015) (nb055_alpha_dummy_017 x y) (nb055_wpp_notmem_0122) (nb055_wpp_notmem_0123 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_014) (nb055_alpha_dummy_016 x y) (nb055_wpp_notmem_0124) (nb055_wpp_notmem_0125 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_080) (nb055_alpha_dummy_081 x y) (nb055_wpp_notmem_0294) (nb055_wpp_notmem_0295 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_002) (nb055_alpha_dummy_003 x y) (nb055_wpp_notmem_0138) (nb055_wpp_notmem_0139 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_001) y (nb055_wpp_notmem_0140) (nb055_wpp_notmem_0141 y) (TEnvFresh.consFresh (nb055_alpha_dummy_000) x (nb055_wpp_notmem_0142) (nb055_wpp_notmem_0143 x) (TEnvFresh.consFresh (nb055_alpha_dummy_004) (nb055_alpha_dummy_005 x y) (nb055_wpp_notmem_0144) (nb055_wpp_notmem_0145 x y) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))

noncomputable def nb055_wpp_refl_0028 (x : Var) (y : Var) : TReflOn [((nb055_alpha_dummy_150), (nb055_alpha_dummy_151 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb055_compact_envfresh_0028 x y)

noncomputable def nb055_split_alpha_0019 (x : Var) (y : Var) : TAlphaWff [((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_148)) (Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb055_alpha_dummy_148)) (Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119))) (syn_csn (syn_c0c))))))))) (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_149 x y)) (Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb055_alpha_dummy_149 x y)) (Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))) (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0162) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0164 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0162) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0164 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0166) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0167 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0163) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0165 x y) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_078))).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_079 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb055_split_alpha_0018 x y))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb055_split_alpha_0018 x y))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_150), (nb055_alpha_dummy_151 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_ccompl (syn_csn (syn_c0c))) (nb055_wpp_refl_0028 x y))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0162) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0164 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0162) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0164 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0166) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0167 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0163) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0165 x y) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_078))).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_079 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb055_split_alpha_0018 x y))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb055_split_alpha_0018 x y))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_150), (nb055_alpha_dummy_151 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_ccompl (syn_csn (syn_c0c))) (nb055_wpp_refl_0028 x y)))))))))))))))))))

theorem nb055_compact_fv_empty_0116 : (nb055_alpha_dummy_170) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0386 : (nb055_alpha_dummy_170) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_170, fv_syn_c1c] using (nb055_compact_fv_empty_0116)

theorem nb055_compact_fv_empty_0117 (x : Var) (y : Var) : (nb055_alpha_dummy_173 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0387 (x : Var) (y : Var) : (nb055_alpha_dummy_173 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_173, fv_syn_c1c] using (nb055_compact_fv_empty_0117 x y)

theorem nb055_compact_fv_empty_0118 : (nb055_alpha_dummy_169) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0388 : (nb055_alpha_dummy_169) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_169, fv_syn_c1c] using (nb055_compact_fv_empty_0118)

theorem nb055_compact_fv_empty_0119 (x : Var) (y : Var) : (nb055_alpha_dummy_172 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0389 (x : Var) (y : Var) : (nb055_alpha_dummy_172 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_172, fv_syn_c1c] using (nb055_compact_fv_empty_0119 x y)

theorem nb055_compact_fv_empty_0120 : (nb055_alpha_dummy_168) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0390 : (nb055_alpha_dummy_168) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_168, fv_syn_c1c] using (nb055_compact_fv_empty_0120)

theorem nb055_compact_fv_empty_0121 (x : Var) (y : Var) : (nb055_alpha_dummy_171 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0391 (x : Var) (y : Var) : (nb055_alpha_dummy_171 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_171, fv_syn_c1c] using (nb055_compact_fv_empty_0121 x y)

theorem nb055_compact_fv_empty_0122 : (nb055_alpha_dummy_166) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0392 : (nb055_alpha_dummy_166) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_166, fv_syn_c1c] using (nb055_compact_fv_empty_0122)

theorem nb055_compact_fv_empty_0123 (x : Var) (y : Var) : (nb055_alpha_dummy_167 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0393 (x : Var) (y : Var) : (nb055_alpha_dummy_167 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_167, fv_syn_c1c] using (nb055_compact_fv_empty_0123 x y)

theorem nb055_compact_fv_empty_0124 : (nb055_alpha_dummy_162) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0394 : (nb055_alpha_dummy_162) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_162, fv_syn_c1c] using (nb055_compact_fv_empty_0124)

theorem nb055_compact_fv_empty_0125 (x : Var) (y : Var) : (nb055_alpha_dummy_164 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0395 (x : Var) (y : Var) : (nb055_alpha_dummy_164 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_164, fv_syn_c1c] using (nb055_compact_fv_empty_0125 x y)

theorem nb055_compact_fv_empty_0126 : (nb055_alpha_dummy_163) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0396 : (nb055_alpha_dummy_163) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_163, fv_syn_c1c] using (nb055_compact_fv_empty_0126)

theorem nb055_compact_fv_empty_0127 (x : Var) (y : Var) : (nb055_alpha_dummy_165 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0397 (x : Var) (y : Var) : (nb055_alpha_dummy_165 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_165, fv_syn_c1c] using (nb055_compact_fv_empty_0127 x y)

theorem nb055_compact_fv_empty_0128 : (nb055_alpha_dummy_155) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0398 : (nb055_alpha_dummy_155) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_155, fv_syn_c1c] using (nb055_compact_fv_empty_0128)

theorem nb055_compact_fv_empty_0129 (x : Var) (y : Var) : (nb055_alpha_dummy_157 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0399 (x : Var) (y : Var) : (nb055_alpha_dummy_157 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_157, fv_syn_c1c] using (nb055_compact_fv_empty_0129 x y)

theorem nb055_compact_fv_empty_0130 : (nb055_alpha_dummy_154) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0400 : (nb055_alpha_dummy_154) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_154, fv_syn_c1c] using (nb055_compact_fv_empty_0130)

theorem nb055_compact_fv_empty_0131 (x : Var) (y : Var) : (nb055_alpha_dummy_156 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0401 (x : Var) (y : Var) : (nb055_alpha_dummy_156 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_156, fv_syn_c1c] using (nb055_compact_fv_empty_0131 x y)

theorem nb055_compact_fv_empty_0132 : (nb055_alpha_dummy_160) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0402 : (nb055_alpha_dummy_160) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_160, fv_syn_c1c] using (nb055_compact_fv_empty_0132)

theorem nb055_compact_fv_empty_0133 (x : Var) (y : Var) : (nb055_alpha_dummy_161 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0403 (x : Var) (y : Var) : (nb055_alpha_dummy_161 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_161, fv_syn_c1c] using (nb055_compact_fv_empty_0133 x y)

theorem nb055_compact_fv_empty_0134 : (nb055_alpha_dummy_158) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0404 : (nb055_alpha_dummy_158) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_158, fv_syn_c1c] using (nb055_compact_fv_empty_0134)

theorem nb055_compact_fv_empty_0135 (x : Var) (y : Var) : (nb055_alpha_dummy_159 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0405 (x : Var) (y : Var) : (nb055_alpha_dummy_159 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_159, fv_syn_c1c] using (nb055_compact_fv_empty_0135 x y)

theorem nb055_compact_envfresh_0029 (x : Var) (y : Var) : TEnvFresh [((nb055_alpha_dummy_170), (nb055_alpha_dummy_173 x y)), ((nb055_alpha_dummy_169), (nb055_alpha_dummy_172 x y)), ((nb055_alpha_dummy_168), (nb055_alpha_dummy_171 x y)), ((nb055_alpha_dummy_166), (nb055_alpha_dummy_167 x y)), ((nb055_alpha_dummy_162), (nb055_alpha_dummy_164 x y)), ((nb055_alpha_dummy_163), (nb055_alpha_dummy_165 x y)), ((nb055_alpha_dummy_155), (nb055_alpha_dummy_157 x y)), ((nb055_alpha_dummy_154), (nb055_alpha_dummy_156 x y)), ((nb055_alpha_dummy_160), (nb055_alpha_dummy_161 x y)), ((nb055_alpha_dummy_158), (nb055_alpha_dummy_159 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb055_alpha_dummy_170) (nb055_alpha_dummy_173 x y) (nb055_wpp_notmem_0386) (nb055_wpp_notmem_0387 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_169) (nb055_alpha_dummy_172 x y) (nb055_wpp_notmem_0388) (nb055_wpp_notmem_0389 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_168) (nb055_alpha_dummy_171 x y) (nb055_wpp_notmem_0390) (nb055_wpp_notmem_0391 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_166) (nb055_alpha_dummy_167 x y) (nb055_wpp_notmem_0392) (nb055_wpp_notmem_0393 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_162) (nb055_alpha_dummy_164 x y) (nb055_wpp_notmem_0394) (nb055_wpp_notmem_0395 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_163) (nb055_alpha_dummy_165 x y) (nb055_wpp_notmem_0396) (nb055_wpp_notmem_0397 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_155) (nb055_alpha_dummy_157 x y) (nb055_wpp_notmem_0398) (nb055_wpp_notmem_0399 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_154) (nb055_alpha_dummy_156 x y) (nb055_wpp_notmem_0400) (nb055_wpp_notmem_0401 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_160) (nb055_alpha_dummy_161 x y) (nb055_wpp_notmem_0402) (nb055_wpp_notmem_0403 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_158) (nb055_alpha_dummy_159 x y) (nb055_wpp_notmem_0404) (nb055_wpp_notmem_0405 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_078) (nb055_alpha_dummy_079 x y) (nb055_wpp_notmem_0316) (nb055_wpp_notmem_0317 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_015) (nb055_alpha_dummy_017 x y) (nb055_wpp_notmem_0012) (nb055_wpp_notmem_0013 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_014) (nb055_alpha_dummy_016 x y) (nb055_wpp_notmem_0014) (nb055_wpp_notmem_0015 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_080) (nb055_alpha_dummy_081 x y) (nb055_wpp_notmem_0226) (nb055_wpp_notmem_0227 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_002) (nb055_alpha_dummy_003 x y) (nb055_wpp_notmem_0028) (nb055_wpp_notmem_0029 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_001) y (nb055_wpp_notmem_0030) (nb055_wpp_notmem_0031 y) (TEnvFresh.consFresh (nb055_alpha_dummy_000) x (nb055_wpp_notmem_0032) (nb055_wpp_notmem_0033 x) (TEnvFresh.consFresh (nb055_alpha_dummy_004) (nb055_alpha_dummy_005 x y) (nb055_wpp_notmem_0034) (nb055_wpp_notmem_0035 x y) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))

noncomputable def nb055_wpp_refl_0029 (x : Var) (y : Var) : TReflOn [((nb055_alpha_dummy_170), (nb055_alpha_dummy_173 x y)), ((nb055_alpha_dummy_169), (nb055_alpha_dummy_172 x y)), ((nb055_alpha_dummy_168), (nb055_alpha_dummy_171 x y)), ((nb055_alpha_dummy_166), (nb055_alpha_dummy_167 x y)), ((nb055_alpha_dummy_162), (nb055_alpha_dummy_164 x y)), ((nb055_alpha_dummy_163), (nb055_alpha_dummy_165 x y)), ((nb055_alpha_dummy_155), (nb055_alpha_dummy_157 x y)), ((nb055_alpha_dummy_154), (nb055_alpha_dummy_156 x y)), ((nb055_alpha_dummy_160), (nb055_alpha_dummy_161 x y)), ((nb055_alpha_dummy_158), (nb055_alpha_dummy_159 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb055_compact_envfresh_0029 x y)

theorem nb055_wpp_notmem_0406 : (nb055_alpha_dummy_170) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_170, fv_syn_c0] using (nb055_compact_fv_empty_0116)

theorem nb055_wpp_notmem_0407 (x : Var) (y : Var) : (nb055_alpha_dummy_173 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_173, fv_syn_c0] using (nb055_compact_fv_empty_0117 x y)

theorem nb055_wpp_notmem_0408 : (nb055_alpha_dummy_169) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_169, fv_syn_c0] using (nb055_compact_fv_empty_0118)

theorem nb055_wpp_notmem_0409 (x : Var) (y : Var) : (nb055_alpha_dummy_172 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_172, fv_syn_c0] using (nb055_compact_fv_empty_0119 x y)

theorem nb055_wpp_notmem_0410 : (nb055_alpha_dummy_168) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_168, fv_syn_c0] using (nb055_compact_fv_empty_0120)

theorem nb055_wpp_notmem_0411 (x : Var) (y : Var) : (nb055_alpha_dummy_171 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_171, fv_syn_c0] using (nb055_compact_fv_empty_0121 x y)

theorem nb055_wpp_notmem_0412 : (nb055_alpha_dummy_166) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_166, fv_syn_c0] using (nb055_compact_fv_empty_0122)

theorem nb055_wpp_notmem_0413 (x : Var) (y : Var) : (nb055_alpha_dummy_167 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_167, fv_syn_c0] using (nb055_compact_fv_empty_0123 x y)

theorem nb055_wpp_notmem_0414 : (nb055_alpha_dummy_162) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_162, fv_syn_c0] using (nb055_compact_fv_empty_0124)

theorem nb055_wpp_notmem_0415 (x : Var) (y : Var) : (nb055_alpha_dummy_164 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_164, fv_syn_c0] using (nb055_compact_fv_empty_0125 x y)

theorem nb055_wpp_notmem_0416 : (nb055_alpha_dummy_163) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_163, fv_syn_c0] using (nb055_compact_fv_empty_0126)

theorem nb055_wpp_notmem_0417 (x : Var) (y : Var) : (nb055_alpha_dummy_165 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_165, fv_syn_c0] using (nb055_compact_fv_empty_0127 x y)

theorem nb055_wpp_notmem_0418 : (nb055_alpha_dummy_155) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_155, fv_syn_c0] using (nb055_compact_fv_empty_0128)

theorem nb055_wpp_notmem_0419 (x : Var) (y : Var) : (nb055_alpha_dummy_157 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_157, fv_syn_c0] using (nb055_compact_fv_empty_0129 x y)

theorem nb055_wpp_notmem_0420 : (nb055_alpha_dummy_154) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_154, fv_syn_c0] using (nb055_compact_fv_empty_0130)

theorem nb055_wpp_notmem_0421 (x : Var) (y : Var) : (nb055_alpha_dummy_156 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_156, fv_syn_c0] using (nb055_compact_fv_empty_0131 x y)

theorem nb055_wpp_notmem_0422 : (nb055_alpha_dummy_160) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_160, fv_syn_c0] using (nb055_compact_fv_empty_0132)

theorem nb055_wpp_notmem_0423 (x : Var) (y : Var) : (nb055_alpha_dummy_161 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_161, fv_syn_c0] using (nb055_compact_fv_empty_0133 x y)

theorem nb055_wpp_notmem_0424 : (nb055_alpha_dummy_158) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_158, fv_syn_c0] using (nb055_compact_fv_empty_0134)

theorem nb055_wpp_notmem_0425 (x : Var) (y : Var) : (nb055_alpha_dummy_159 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_159, fv_syn_c0] using (nb055_compact_fv_empty_0135 x y)

theorem nb055_compact_envfresh_0030 (x : Var) (y : Var) : TEnvFresh [((nb055_alpha_dummy_170), (nb055_alpha_dummy_173 x y)), ((nb055_alpha_dummy_169), (nb055_alpha_dummy_172 x y)), ((nb055_alpha_dummy_168), (nb055_alpha_dummy_171 x y)), ((nb055_alpha_dummy_166), (nb055_alpha_dummy_167 x y)), ((nb055_alpha_dummy_162), (nb055_alpha_dummy_164 x y)), ((nb055_alpha_dummy_163), (nb055_alpha_dummy_165 x y)), ((nb055_alpha_dummy_155), (nb055_alpha_dummy_157 x y)), ((nb055_alpha_dummy_154), (nb055_alpha_dummy_156 x y)), ((nb055_alpha_dummy_160), (nb055_alpha_dummy_161 x y)), ((nb055_alpha_dummy_158), (nb055_alpha_dummy_159 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb055_alpha_dummy_170) (nb055_alpha_dummy_173 x y) (nb055_wpp_notmem_0406) (nb055_wpp_notmem_0407 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_169) (nb055_alpha_dummy_172 x y) (nb055_wpp_notmem_0408) (nb055_wpp_notmem_0409 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_168) (nb055_alpha_dummy_171 x y) (nb055_wpp_notmem_0410) (nb055_wpp_notmem_0411 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_166) (nb055_alpha_dummy_167 x y) (nb055_wpp_notmem_0412) (nb055_wpp_notmem_0413 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_162) (nb055_alpha_dummy_164 x y) (nb055_wpp_notmem_0414) (nb055_wpp_notmem_0415 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_163) (nb055_alpha_dummy_165 x y) (nb055_wpp_notmem_0416) (nb055_wpp_notmem_0417 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_155) (nb055_alpha_dummy_157 x y) (nb055_wpp_notmem_0418) (nb055_wpp_notmem_0419 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_154) (nb055_alpha_dummy_156 x y) (nb055_wpp_notmem_0420) (nb055_wpp_notmem_0421 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_160) (nb055_alpha_dummy_161 x y) (nb055_wpp_notmem_0422) (nb055_wpp_notmem_0423 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_158) (nb055_alpha_dummy_159 x y) (nb055_wpp_notmem_0424) (nb055_wpp_notmem_0425 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_078) (nb055_alpha_dummy_079 x y) (nb055_wpp_notmem_0338) (nb055_wpp_notmem_0339 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_015) (nb055_alpha_dummy_017 x y) (nb055_wpp_notmem_0048) (nb055_wpp_notmem_0049 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_014) (nb055_alpha_dummy_016 x y) (nb055_wpp_notmem_0050) (nb055_wpp_notmem_0051 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_080) (nb055_alpha_dummy_081 x y) (nb055_wpp_notmem_0248) (nb055_wpp_notmem_0249 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_002) (nb055_alpha_dummy_003 x y) (nb055_wpp_notmem_0064) (nb055_wpp_notmem_0065 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_001) y (nb055_wpp_notmem_0066) (nb055_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb055_alpha_dummy_000) x (nb055_wpp_notmem_0068) (nb055_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb055_alpha_dummy_004) (nb055_alpha_dummy_005 x y) (nb055_wpp_notmem_0070) (nb055_wpp_notmem_0071 x y) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))

noncomputable def nb055_wpp_refl_0030 (x : Var) (y : Var) : TReflOn [((nb055_alpha_dummy_170), (nb055_alpha_dummy_173 x y)), ((nb055_alpha_dummy_169), (nb055_alpha_dummy_172 x y)), ((nb055_alpha_dummy_168), (nb055_alpha_dummy_171 x y)), ((nb055_alpha_dummy_166), (nb055_alpha_dummy_167 x y)), ((nb055_alpha_dummy_162), (nb055_alpha_dummy_164 x y)), ((nb055_alpha_dummy_163), (nb055_alpha_dummy_165 x y)), ((nb055_alpha_dummy_155), (nb055_alpha_dummy_157 x y)), ((nb055_alpha_dummy_154), (nb055_alpha_dummy_156 x y)), ((nb055_alpha_dummy_160), (nb055_alpha_dummy_161 x y)), ((nb055_alpha_dummy_158), (nb055_alpha_dummy_159 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb055_compact_envfresh_0030 x y)

noncomputable def nb055_split_alpha_0020 (x : Var) (y : Var) : TAlphaWff [((nb055_alpha_dummy_170), (nb055_alpha_dummy_173 x y)), ((nb055_alpha_dummy_169), (nb055_alpha_dummy_172 x y)), ((nb055_alpha_dummy_168), (nb055_alpha_dummy_171 x y)), ((nb055_alpha_dummy_166), (nb055_alpha_dummy_167 x y)), ((nb055_alpha_dummy_162), (nb055_alpha_dummy_164 x y)), ((nb055_alpha_dummy_163), (nb055_alpha_dummy_165 x y)), ((nb055_alpha_dummy_155), (nb055_alpha_dummy_157 x y)), ((nb055_alpha_dummy_154), (nb055_alpha_dummy_156 x y)), ((nb055_alpha_dummy_160), (nb055_alpha_dummy_161 x y)), ((nb055_alpha_dummy_158), (nb055_alpha_dummy_159 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb055_alpha_dummy_169)) (Class.cv (nb055_alpha_dummy_170))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_168)) (syn_cun (Class.cv (nb055_alpha_dummy_169)) (Class.cv (nb055_alpha_dummy_170)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb055_alpha_dummy_172 x y)) (Class.cv (nb055_alpha_dummy_173 x y))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_171 x y)) (syn_cun (Class.cv (nb055_alpha_dummy_172 x y)) (Class.cv (nb055_alpha_dummy_173 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0188) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0189 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0186) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0187 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0192) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0193 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0190) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0191 x y) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0188) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0189 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0186) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0187 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0192) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0193 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0190) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0191 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_170), (nb055_alpha_dummy_173 x y)), ((nb055_alpha_dummy_169), (nb055_alpha_dummy_172 x y)), ((nb055_alpha_dummy_168), (nb055_alpha_dummy_171 x y)), ((nb055_alpha_dummy_166), (nb055_alpha_dummy_167 x y)), ((nb055_alpha_dummy_162), (nb055_alpha_dummy_164 x y)), ((nb055_alpha_dummy_163), (nb055_alpha_dummy_165 x y)), ((nb055_alpha_dummy_155), (nb055_alpha_dummy_157 x y)), ((nb055_alpha_dummy_154), (nb055_alpha_dummy_156 x y)), ((nb055_alpha_dummy_160), (nb055_alpha_dummy_161 x y)), ((nb055_alpha_dummy_158), (nb055_alpha_dummy_159 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_c0) (nb055_wpp_refl_0030 x y))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0196) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0197 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0194) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0195 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0196) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0197 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0194) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0195 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0200) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0201 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0198) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0199 x y) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0200) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0201 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0198) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0199 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb055_wpp_notmem_0426 : (nb055_alpha_dummy_166) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_166, fv_syn_cnnc] using (nb055_compact_fv_empty_0122)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
