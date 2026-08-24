import NAR4C055C001Part009

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

noncomputable def nb055_split_alpha_0014 (x : Var) (y : Var) : TAlphaWff [((nb055_alpha_dummy_112), (nb055_alpha_dummy_113 x y)), ((nb055_alpha_dummy_086), (nb055_alpha_dummy_087 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_112)) (Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb055_alpha_dummy_112)) (Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083))) (syn_csn (syn_c0c))))))))) (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_113 x y)) (Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb055_alpha_dummy_113 x y)) (Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))) (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0124) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0126 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0124) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0126 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0128) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0129 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0125) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0127 x y) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_017 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb055_split_alpha_0013 x y))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb055_split_alpha_0013 x y))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_114), (nb055_alpha_dummy_115 x y)), ((nb055_alpha_dummy_083), (nb055_alpha_dummy_085 x y)), ((nb055_alpha_dummy_082), (nb055_alpha_dummy_084 x y)), ((nb055_alpha_dummy_112), (nb055_alpha_dummy_113 x y)), ((nb055_alpha_dummy_086), (nb055_alpha_dummy_087 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_ccompl (syn_csn (syn_c0c))) (nb055_wpp_refl_0021 x y))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0124) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0126 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0124) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0126 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0128) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0129 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0125) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0127 x y) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_017 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb055_split_alpha_0013 x y))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb055_split_alpha_0013 x y))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_114), (nb055_alpha_dummy_115 x y)), ((nb055_alpha_dummy_083), (nb055_alpha_dummy_085 x y)), ((nb055_alpha_dummy_082), (nb055_alpha_dummy_084 x y)), ((nb055_alpha_dummy_112), (nb055_alpha_dummy_113 x y)), ((nb055_alpha_dummy_086), (nb055_alpha_dummy_087 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_ccompl (syn_csn (syn_c0c))) (nb055_wpp_refl_0021 x y)))))))))))))))))))

theorem nb055_compact_fv_empty_0088 : (nb055_alpha_dummy_134) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0296 : (nb055_alpha_dummy_134) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_134, fv_syn_c1c] using (nb055_compact_fv_empty_0088)

theorem nb055_compact_fv_empty_0089 (x : Var) (y : Var) : (nb055_alpha_dummy_137 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0297 (x : Var) (y : Var) : (nb055_alpha_dummy_137 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_137, fv_syn_c1c] using (nb055_compact_fv_empty_0089 x y)

theorem nb055_compact_fv_empty_0090 : (nb055_alpha_dummy_133) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0298 : (nb055_alpha_dummy_133) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_133, fv_syn_c1c] using (nb055_compact_fv_empty_0090)

theorem nb055_compact_fv_empty_0091 (x : Var) (y : Var) : (nb055_alpha_dummy_136 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0299 (x : Var) (y : Var) : (nb055_alpha_dummy_136 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_136, fv_syn_c1c] using (nb055_compact_fv_empty_0091 x y)

theorem nb055_compact_fv_empty_0092 : (nb055_alpha_dummy_132) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0300 : (nb055_alpha_dummy_132) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_132, fv_syn_c1c] using (nb055_compact_fv_empty_0092)

theorem nb055_compact_fv_empty_0093 (x : Var) (y : Var) : (nb055_alpha_dummy_135 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0301 (x : Var) (y : Var) : (nb055_alpha_dummy_135 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_135, fv_syn_c1c] using (nb055_compact_fv_empty_0093 x y)

theorem nb055_compact_fv_empty_0094 : (nb055_alpha_dummy_130) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0302 : (nb055_alpha_dummy_130) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_130, fv_syn_c1c] using (nb055_compact_fv_empty_0094)

theorem nb055_compact_fv_empty_0095 (x : Var) (y : Var) : (nb055_alpha_dummy_131 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0303 (x : Var) (y : Var) : (nb055_alpha_dummy_131 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_131, fv_syn_c1c] using (nb055_compact_fv_empty_0095 x y)

theorem nb055_compact_fv_empty_0096 : (nb055_alpha_dummy_126) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0304 : (nb055_alpha_dummy_126) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_126, fv_syn_c1c] using (nb055_compact_fv_empty_0096)

theorem nb055_compact_fv_empty_0097 (x : Var) (y : Var) : (nb055_alpha_dummy_128 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0305 (x : Var) (y : Var) : (nb055_alpha_dummy_128 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_128, fv_syn_c1c] using (nb055_compact_fv_empty_0097 x y)

theorem nb055_compact_fv_empty_0098 : (nb055_alpha_dummy_127) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0306 : (nb055_alpha_dummy_127) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_127, fv_syn_c1c] using (nb055_compact_fv_empty_0098)

theorem nb055_compact_fv_empty_0099 (x : Var) (y : Var) : (nb055_alpha_dummy_129 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0307 (x : Var) (y : Var) : (nb055_alpha_dummy_129 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_129, fv_syn_c1c] using (nb055_compact_fv_empty_0099 x y)

theorem nb055_compact_fv_empty_0100 : (nb055_alpha_dummy_119) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0308 : (nb055_alpha_dummy_119) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_119, fv_syn_c1c] using (nb055_compact_fv_empty_0100)

theorem nb055_compact_fv_empty_0101 (x : Var) (y : Var) : (nb055_alpha_dummy_121 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0309 (x : Var) (y : Var) : (nb055_alpha_dummy_121 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_121, fv_syn_c1c] using (nb055_compact_fv_empty_0101 x y)

theorem nb055_compact_fv_empty_0102 : (nb055_alpha_dummy_118) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0310 : (nb055_alpha_dummy_118) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_118, fv_syn_c1c] using (nb055_compact_fv_empty_0102)

theorem nb055_compact_fv_empty_0103 (x : Var) (y : Var) : (nb055_alpha_dummy_120 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0311 (x : Var) (y : Var) : (nb055_alpha_dummy_120 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_120, fv_syn_c1c] using (nb055_compact_fv_empty_0103 x y)

theorem nb055_compact_fv_empty_0104 : (nb055_alpha_dummy_124) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0312 : (nb055_alpha_dummy_124) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_124, fv_syn_c1c] using (nb055_compact_fv_empty_0104)

theorem nb055_compact_fv_empty_0105 (x : Var) (y : Var) : (nb055_alpha_dummy_125 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0313 (x : Var) (y : Var) : (nb055_alpha_dummy_125 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_125, fv_syn_c1c] using (nb055_compact_fv_empty_0105 x y)

theorem nb055_compact_fv_empty_0106 : (nb055_alpha_dummy_122) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0314 : (nb055_alpha_dummy_122) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_122, fv_syn_c1c] using (nb055_compact_fv_empty_0106)

theorem nb055_compact_fv_empty_0107 (x : Var) (y : Var) : (nb055_alpha_dummy_123 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0315 (x : Var) (y : Var) : (nb055_alpha_dummy_123 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_123, fv_syn_c1c] using (nb055_compact_fv_empty_0107 x y)

theorem nb055_compact_fv_empty_0108 : (nb055_alpha_dummy_078) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0316 : (nb055_alpha_dummy_078) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_078, fv_syn_c1c] using (nb055_compact_fv_empty_0108)

theorem nb055_compact_fv_empty_0109 (x : Var) (y : Var) : (nb055_alpha_dummy_079 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0317 (x : Var) (y : Var) : (nb055_alpha_dummy_079 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_079, fv_syn_c1c] using (nb055_compact_fv_empty_0109 x y)

theorem nb055_compact_envfresh_0022 (x : Var) (y : Var) : TEnvFresh [((nb055_alpha_dummy_134), (nb055_alpha_dummy_137 x y)), ((nb055_alpha_dummy_133), (nb055_alpha_dummy_136 x y)), ((nb055_alpha_dummy_132), (nb055_alpha_dummy_135 x y)), ((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)), ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)), ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_124), (nb055_alpha_dummy_125 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb055_alpha_dummy_134) (nb055_alpha_dummy_137 x y) (nb055_wpp_notmem_0296) (nb055_wpp_notmem_0297 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_133) (nb055_alpha_dummy_136 x y) (nb055_wpp_notmem_0298) (nb055_wpp_notmem_0299 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_132) (nb055_alpha_dummy_135 x y) (nb055_wpp_notmem_0300) (nb055_wpp_notmem_0301 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_130) (nb055_alpha_dummy_131 x y) (nb055_wpp_notmem_0302) (nb055_wpp_notmem_0303 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_126) (nb055_alpha_dummy_128 x y) (nb055_wpp_notmem_0304) (nb055_wpp_notmem_0305 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_127) (nb055_alpha_dummy_129 x y) (nb055_wpp_notmem_0306) (nb055_wpp_notmem_0307 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_119) (nb055_alpha_dummy_121 x y) (nb055_wpp_notmem_0308) (nb055_wpp_notmem_0309 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_118) (nb055_alpha_dummy_120 x y) (nb055_wpp_notmem_0310) (nb055_wpp_notmem_0311 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_124) (nb055_alpha_dummy_125 x y) (nb055_wpp_notmem_0312) (nb055_wpp_notmem_0313 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_122) (nb055_alpha_dummy_123 x y) (nb055_wpp_notmem_0314) (nb055_wpp_notmem_0315 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_078) (nb055_alpha_dummy_079 x y) (nb055_wpp_notmem_0316) (nb055_wpp_notmem_0317 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_015) (nb055_alpha_dummy_017 x y) (nb055_wpp_notmem_0012) (nb055_wpp_notmem_0013 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_014) (nb055_alpha_dummy_016 x y) (nb055_wpp_notmem_0014) (nb055_wpp_notmem_0015 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_080) (nb055_alpha_dummy_081 x y) (nb055_wpp_notmem_0226) (nb055_wpp_notmem_0227 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_002) (nb055_alpha_dummy_003 x y) (nb055_wpp_notmem_0028) (nb055_wpp_notmem_0029 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_001) y (nb055_wpp_notmem_0030) (nb055_wpp_notmem_0031 y) (TEnvFresh.consFresh (nb055_alpha_dummy_000) x (nb055_wpp_notmem_0032) (nb055_wpp_notmem_0033 x) (TEnvFresh.consFresh (nb055_alpha_dummy_004) (nb055_alpha_dummy_005 x y) (nb055_wpp_notmem_0034) (nb055_wpp_notmem_0035 x y) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))

noncomputable def nb055_wpp_refl_0022 (x : Var) (y : Var) : TReflOn [((nb055_alpha_dummy_134), (nb055_alpha_dummy_137 x y)), ((nb055_alpha_dummy_133), (nb055_alpha_dummy_136 x y)), ((nb055_alpha_dummy_132), (nb055_alpha_dummy_135 x y)), ((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)), ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)), ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_124), (nb055_alpha_dummy_125 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb055_compact_envfresh_0022 x y)

theorem nb055_wpp_notmem_0318 : (nb055_alpha_dummy_134) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_134, fv_syn_c0] using (nb055_compact_fv_empty_0088)

theorem nb055_wpp_notmem_0319 (x : Var) (y : Var) : (nb055_alpha_dummy_137 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_137, fv_syn_c0] using (nb055_compact_fv_empty_0089 x y)

theorem nb055_wpp_notmem_0320 : (nb055_alpha_dummy_133) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_133, fv_syn_c0] using (nb055_compact_fv_empty_0090)

theorem nb055_wpp_notmem_0321 (x : Var) (y : Var) : (nb055_alpha_dummy_136 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_136, fv_syn_c0] using (nb055_compact_fv_empty_0091 x y)

theorem nb055_wpp_notmem_0322 : (nb055_alpha_dummy_132) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_132, fv_syn_c0] using (nb055_compact_fv_empty_0092)

theorem nb055_wpp_notmem_0323 (x : Var) (y : Var) : (nb055_alpha_dummy_135 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_135, fv_syn_c0] using (nb055_compact_fv_empty_0093 x y)

theorem nb055_wpp_notmem_0324 : (nb055_alpha_dummy_130) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_130, fv_syn_c0] using (nb055_compact_fv_empty_0094)

theorem nb055_wpp_notmem_0325 (x : Var) (y : Var) : (nb055_alpha_dummy_131 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_131, fv_syn_c0] using (nb055_compact_fv_empty_0095 x y)

theorem nb055_wpp_notmem_0326 : (nb055_alpha_dummy_126) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_126, fv_syn_c0] using (nb055_compact_fv_empty_0096)

theorem nb055_wpp_notmem_0327 (x : Var) (y : Var) : (nb055_alpha_dummy_128 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_128, fv_syn_c0] using (nb055_compact_fv_empty_0097 x y)

theorem nb055_wpp_notmem_0328 : (nb055_alpha_dummy_127) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_127, fv_syn_c0] using (nb055_compact_fv_empty_0098)

theorem nb055_wpp_notmem_0329 (x : Var) (y : Var) : (nb055_alpha_dummy_129 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_129, fv_syn_c0] using (nb055_compact_fv_empty_0099 x y)

theorem nb055_wpp_notmem_0330 : (nb055_alpha_dummy_119) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_119, fv_syn_c0] using (nb055_compact_fv_empty_0100)

theorem nb055_wpp_notmem_0331 (x : Var) (y : Var) : (nb055_alpha_dummy_121 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_121, fv_syn_c0] using (nb055_compact_fv_empty_0101 x y)

theorem nb055_wpp_notmem_0332 : (nb055_alpha_dummy_118) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_118, fv_syn_c0] using (nb055_compact_fv_empty_0102)

theorem nb055_wpp_notmem_0333 (x : Var) (y : Var) : (nb055_alpha_dummy_120 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_120, fv_syn_c0] using (nb055_compact_fv_empty_0103 x y)

theorem nb055_wpp_notmem_0334 : (nb055_alpha_dummy_124) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_124, fv_syn_c0] using (nb055_compact_fv_empty_0104)

theorem nb055_wpp_notmem_0335 (x : Var) (y : Var) : (nb055_alpha_dummy_125 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_125, fv_syn_c0] using (nb055_compact_fv_empty_0105 x y)

theorem nb055_wpp_notmem_0336 : (nb055_alpha_dummy_122) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_122, fv_syn_c0] using (nb055_compact_fv_empty_0106)

theorem nb055_wpp_notmem_0337 (x : Var) (y : Var) : (nb055_alpha_dummy_123 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_123, fv_syn_c0] using (nb055_compact_fv_empty_0107 x y)

theorem nb055_wpp_notmem_0338 : (nb055_alpha_dummy_078) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_078, fv_syn_c0] using (nb055_compact_fv_empty_0108)

theorem nb055_wpp_notmem_0339 (x : Var) (y : Var) : (nb055_alpha_dummy_079 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_079, fv_syn_c0] using (nb055_compact_fv_empty_0109 x y)

theorem nb055_compact_envfresh_0023 (x : Var) (y : Var) : TEnvFresh [((nb055_alpha_dummy_134), (nb055_alpha_dummy_137 x y)), ((nb055_alpha_dummy_133), (nb055_alpha_dummy_136 x y)), ((nb055_alpha_dummy_132), (nb055_alpha_dummy_135 x y)), ((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)), ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)), ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_124), (nb055_alpha_dummy_125 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb055_alpha_dummy_134) (nb055_alpha_dummy_137 x y) (nb055_wpp_notmem_0318) (nb055_wpp_notmem_0319 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_133) (nb055_alpha_dummy_136 x y) (nb055_wpp_notmem_0320) (nb055_wpp_notmem_0321 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_132) (nb055_alpha_dummy_135 x y) (nb055_wpp_notmem_0322) (nb055_wpp_notmem_0323 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_130) (nb055_alpha_dummy_131 x y) (nb055_wpp_notmem_0324) (nb055_wpp_notmem_0325 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_126) (nb055_alpha_dummy_128 x y) (nb055_wpp_notmem_0326) (nb055_wpp_notmem_0327 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_127) (nb055_alpha_dummy_129 x y) (nb055_wpp_notmem_0328) (nb055_wpp_notmem_0329 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_119) (nb055_alpha_dummy_121 x y) (nb055_wpp_notmem_0330) (nb055_wpp_notmem_0331 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_118) (nb055_alpha_dummy_120 x y) (nb055_wpp_notmem_0332) (nb055_wpp_notmem_0333 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_124) (nb055_alpha_dummy_125 x y) (nb055_wpp_notmem_0334) (nb055_wpp_notmem_0335 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_122) (nb055_alpha_dummy_123 x y) (nb055_wpp_notmem_0336) (nb055_wpp_notmem_0337 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_078) (nb055_alpha_dummy_079 x y) (nb055_wpp_notmem_0338) (nb055_wpp_notmem_0339 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_015) (nb055_alpha_dummy_017 x y) (nb055_wpp_notmem_0048) (nb055_wpp_notmem_0049 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_014) (nb055_alpha_dummy_016 x y) (nb055_wpp_notmem_0050) (nb055_wpp_notmem_0051 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_080) (nb055_alpha_dummy_081 x y) (nb055_wpp_notmem_0248) (nb055_wpp_notmem_0249 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_002) (nb055_alpha_dummy_003 x y) (nb055_wpp_notmem_0064) (nb055_wpp_notmem_0065 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_001) y (nb055_wpp_notmem_0066) (nb055_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb055_alpha_dummy_000) x (nb055_wpp_notmem_0068) (nb055_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb055_alpha_dummy_004) (nb055_alpha_dummy_005 x y) (nb055_wpp_notmem_0070) (nb055_wpp_notmem_0071 x y) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))

noncomputable def nb055_wpp_refl_0023 (x : Var) (y : Var) : TReflOn [((nb055_alpha_dummy_134), (nb055_alpha_dummy_137 x y)), ((nb055_alpha_dummy_133), (nb055_alpha_dummy_136 x y)), ((nb055_alpha_dummy_132), (nb055_alpha_dummy_135 x y)), ((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)), ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)), ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_124), (nb055_alpha_dummy_125 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb055_compact_envfresh_0023 x y)

noncomputable def nb055_split_alpha_0015 (x : Var) (y : Var) : TAlphaWff [((nb055_alpha_dummy_134), (nb055_alpha_dummy_137 x y)), ((nb055_alpha_dummy_133), (nb055_alpha_dummy_136 x y)), ((nb055_alpha_dummy_132), (nb055_alpha_dummy_135 x y)), ((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)), ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)), ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_124), (nb055_alpha_dummy_125 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb055_alpha_dummy_133)) (Class.cv (nb055_alpha_dummy_134))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_132)) (syn_cun (Class.cv (nb055_alpha_dummy_133)) (Class.cv (nb055_alpha_dummy_134)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb055_alpha_dummy_136 x y)) (Class.cv (nb055_alpha_dummy_137 x y))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_135 x y)) (syn_cun (Class.cv (nb055_alpha_dummy_136 x y)) (Class.cv (nb055_alpha_dummy_137 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0148) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0149 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0147 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0152) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0153 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0150) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0151 x y) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0148) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0149 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0147 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0152) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0153 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0150) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0151 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_134), (nb055_alpha_dummy_137 x y)), ((nb055_alpha_dummy_133), (nb055_alpha_dummy_136 x y)), ((nb055_alpha_dummy_132), (nb055_alpha_dummy_135 x y)), ((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)), ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)), ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_124), (nb055_alpha_dummy_125 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_c0) (nb055_wpp_refl_0023 x y))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0156) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0157 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0154) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0155 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0156) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0157 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0154) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0155 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0160) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0161 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0158) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0159 x y) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0160) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0161 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0158) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0159 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb055_wpp_notmem_0340 : (nb055_alpha_dummy_130) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_130, fv_syn_cnnc] using (nb055_compact_fv_empty_0094)

theorem nb055_wpp_notmem_0341 (x : Var) (y : Var) : (nb055_alpha_dummy_131 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_131, fv_syn_cnnc] using (nb055_compact_fv_empty_0095 x y)

theorem nb055_wpp_notmem_0342 : (nb055_alpha_dummy_126) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_126, fv_syn_cnnc] using (nb055_compact_fv_empty_0096)

theorem nb055_wpp_notmem_0343 (x : Var) (y : Var) : (nb055_alpha_dummy_128 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_128, fv_syn_cnnc] using (nb055_compact_fv_empty_0097 x y)

theorem nb055_wpp_notmem_0344 : (nb055_alpha_dummy_127) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_127, fv_syn_cnnc] using (nb055_compact_fv_empty_0098)

theorem nb055_wpp_notmem_0345 (x : Var) (y : Var) : (nb055_alpha_dummy_129 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_129, fv_syn_cnnc] using (nb055_compact_fv_empty_0099 x y)

theorem nb055_wpp_notmem_0346 : (nb055_alpha_dummy_119) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_119, fv_syn_cnnc] using (nb055_compact_fv_empty_0100)

theorem nb055_wpp_notmem_0347 (x : Var) (y : Var) : (nb055_alpha_dummy_121 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_121, fv_syn_cnnc] using (nb055_compact_fv_empty_0101 x y)

theorem nb055_wpp_notmem_0348 : (nb055_alpha_dummy_118) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_118, fv_syn_cnnc] using (nb055_compact_fv_empty_0102)

theorem nb055_wpp_notmem_0349 (x : Var) (y : Var) : (nb055_alpha_dummy_120 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_120, fv_syn_cnnc] using (nb055_compact_fv_empty_0103 x y)

theorem nb055_wpp_notmem_0350 : (nb055_alpha_dummy_124) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_124, fv_syn_cnnc] using (nb055_compact_fv_empty_0104)

theorem nb055_wpp_notmem_0351 (x : Var) (y : Var) : (nb055_alpha_dummy_125 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_125, fv_syn_cnnc] using (nb055_compact_fv_empty_0105 x y)

theorem nb055_wpp_notmem_0352 : (nb055_alpha_dummy_122) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_122, fv_syn_cnnc] using (nb055_compact_fv_empty_0106)

theorem nb055_wpp_notmem_0353 (x : Var) (y : Var) : (nb055_alpha_dummy_123 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_123, fv_syn_cnnc] using (nb055_compact_fv_empty_0107 x y)

theorem nb055_wpp_notmem_0354 : (nb055_alpha_dummy_078) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_078, fv_syn_cnnc] using (nb055_compact_fv_empty_0108)

theorem nb055_wpp_notmem_0355 (x : Var) (y : Var) : (nb055_alpha_dummy_079 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_079, fv_syn_cnnc] using (nb055_compact_fv_empty_0109 x y)

theorem nb055_compact_envfresh_0024 (x : Var) (y : Var) : TEnvFresh [((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)), ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)), ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_124), (nb055_alpha_dummy_125 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb055_alpha_dummy_130) (nb055_alpha_dummy_131 x y) (nb055_wpp_notmem_0340) (nb055_wpp_notmem_0341 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_126) (nb055_alpha_dummy_128 x y) (nb055_wpp_notmem_0342) (nb055_wpp_notmem_0343 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_127) (nb055_alpha_dummy_129 x y) (nb055_wpp_notmem_0344) (nb055_wpp_notmem_0345 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_119) (nb055_alpha_dummy_121 x y) (nb055_wpp_notmem_0346) (nb055_wpp_notmem_0347 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_118) (nb055_alpha_dummy_120 x y) (nb055_wpp_notmem_0348) (nb055_wpp_notmem_0349 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_124) (nb055_alpha_dummy_125 x y) (nb055_wpp_notmem_0350) (nb055_wpp_notmem_0351 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_122) (nb055_alpha_dummy_123 x y) (nb055_wpp_notmem_0352) (nb055_wpp_notmem_0353 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_078) (nb055_alpha_dummy_079 x y) (nb055_wpp_notmem_0354) (nb055_wpp_notmem_0355 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_015) (nb055_alpha_dummy_017 x y) (nb055_wpp_notmem_0078) (nb055_wpp_notmem_0079 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_014) (nb055_alpha_dummy_016 x y) (nb055_wpp_notmem_0080) (nb055_wpp_notmem_0081 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_080) (nb055_alpha_dummy_081 x y) (nb055_wpp_notmem_0264) (nb055_wpp_notmem_0265 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_002) (nb055_alpha_dummy_003 x y) (nb055_wpp_notmem_0094) (nb055_wpp_notmem_0095 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_001) y (nb055_wpp_notmem_0096) (nb055_wpp_notmem_0097 y) (TEnvFresh.consFresh (nb055_alpha_dummy_000) x (nb055_wpp_notmem_0098) (nb055_wpp_notmem_0099 x) (TEnvFresh.consFresh (nb055_alpha_dummy_004) (nb055_alpha_dummy_005 x y) (nb055_wpp_notmem_0100) (nb055_wpp_notmem_0101 x y) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))

noncomputable def nb055_wpp_refl_0024 (x : Var) (y : Var) : TReflOn [((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)), ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)), ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_124), (nb055_alpha_dummy_125 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb055_compact_envfresh_0024 x y)

noncomputable def nb055_split_alpha_0016 (x : Var) (y : Var) : TAlphaWff [((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_124), (nb055_alpha_dummy_125 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cphi (Class.cv (nb055_alpha_dummy_119)))) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_078))).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_079 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0140) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0141 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0140) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0141 x y) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_119))).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_121 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0144) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0145 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0144) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0145 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0142) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0143 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_134), (nb055_alpha_dummy_137 x y)), ((nb055_alpha_dummy_133), (nb055_alpha_dummy_136 x y)), ((nb055_alpha_dummy_132), (nb055_alpha_dummy_135 x y)), ((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)), ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)), ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_124), (nb055_alpha_dummy_125 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_c1c) (nb055_wpp_refl_0022 x y))) (TAlphaWff.neg (TAlphaWff.neg (nb055_split_alpha_0015 x y)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0142) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0143 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)), ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)), ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_124), (nb055_alpha_dummy_125 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_cnnc) (nb055_wpp_refl_0024 x y))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0142) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0143 x y) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0142) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0143 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)), ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)), ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_124), (nb055_alpha_dummy_125 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_cnnc) (nb055_wpp_refl_0024 x y))))))))))))))))))

theorem nb055_compact_fv_empty_0110 : (nb055_alpha_dummy_152) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0356 : (nb055_alpha_dummy_152) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_152, fv_syn_c1c] using (nb055_compact_fv_empty_0110)

theorem nb055_compact_fv_empty_0111 (x : Var) (y : Var) : (nb055_alpha_dummy_153 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0357 (x : Var) (y : Var) : (nb055_alpha_dummy_153 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_153, fv_syn_c1c] using (nb055_compact_fv_empty_0111 x y)

theorem nb055_compact_fv_empty_0112 : (nb055_alpha_dummy_150) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0358 : (nb055_alpha_dummy_150) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_150, fv_syn_c1c] using (nb055_compact_fv_empty_0112)

theorem nb055_compact_fv_empty_0113 (x : Var) (y : Var) : (nb055_alpha_dummy_151 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0359 (x : Var) (y : Var) : (nb055_alpha_dummy_151 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_151, fv_syn_c1c] using (nb055_compact_fv_empty_0113 x y)

theorem nb055_compact_fv_empty_0114 : (nb055_alpha_dummy_148) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0360 : (nb055_alpha_dummy_148) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_148, fv_syn_c1c] using (nb055_compact_fv_empty_0114)

theorem nb055_compact_fv_empty_0115 (x : Var) (y : Var) : (nb055_alpha_dummy_149 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0361 (x : Var) (y : Var) : (nb055_alpha_dummy_149 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_149, fv_syn_c1c] using (nb055_compact_fv_empty_0115 x y)

theorem nb055_compact_envfresh_0025 (x : Var) (y : Var) : TEnvFresh [((nb055_alpha_dummy_134), (nb055_alpha_dummy_137 x y)), ((nb055_alpha_dummy_133), (nb055_alpha_dummy_136 x y)), ((nb055_alpha_dummy_132), (nb055_alpha_dummy_135 x y)), ((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)), ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)), ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)), ((nb055_alpha_dummy_152), (nb055_alpha_dummy_153 x y)), ((nb055_alpha_dummy_150), (nb055_alpha_dummy_151 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb055_alpha_dummy_134) (nb055_alpha_dummy_137 x y) (nb055_wpp_notmem_0296) (nb055_wpp_notmem_0297 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_133) (nb055_alpha_dummy_136 x y) (nb055_wpp_notmem_0298) (nb055_wpp_notmem_0299 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_132) (nb055_alpha_dummy_135 x y) (nb055_wpp_notmem_0300) (nb055_wpp_notmem_0301 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_130) (nb055_alpha_dummy_131 x y) (nb055_wpp_notmem_0302) (nb055_wpp_notmem_0303 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_126) (nb055_alpha_dummy_128 x y) (nb055_wpp_notmem_0304) (nb055_wpp_notmem_0305 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_127) (nb055_alpha_dummy_129 x y) (nb055_wpp_notmem_0306) (nb055_wpp_notmem_0307 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_152) (nb055_alpha_dummy_153 x y) (nb055_wpp_notmem_0356) (nb055_wpp_notmem_0357 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_150) (nb055_alpha_dummy_151 x y) (nb055_wpp_notmem_0358) (nb055_wpp_notmem_0359 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_119) (nb055_alpha_dummy_121 x y) (nb055_wpp_notmem_0308) (nb055_wpp_notmem_0309 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_118) (nb055_alpha_dummy_120 x y) (nb055_wpp_notmem_0310) (nb055_wpp_notmem_0311 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_148) (nb055_alpha_dummy_149 x y) (nb055_wpp_notmem_0360) (nb055_wpp_notmem_0361 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_122) (nb055_alpha_dummy_123 x y) (nb055_wpp_notmem_0314) (nb055_wpp_notmem_0315 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_078) (nb055_alpha_dummy_079 x y) (nb055_wpp_notmem_0316) (nb055_wpp_notmem_0317 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_015) (nb055_alpha_dummy_017 x y) (nb055_wpp_notmem_0012) (nb055_wpp_notmem_0013 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_014) (nb055_alpha_dummy_016 x y) (nb055_wpp_notmem_0014) (nb055_wpp_notmem_0015 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_080) (nb055_alpha_dummy_081 x y) (nb055_wpp_notmem_0226) (nb055_wpp_notmem_0227 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_002) (nb055_alpha_dummy_003 x y) (nb055_wpp_notmem_0028) (nb055_wpp_notmem_0029 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_001) y (nb055_wpp_notmem_0030) (nb055_wpp_notmem_0031 y) (TEnvFresh.consFresh (nb055_alpha_dummy_000) x (nb055_wpp_notmem_0032) (nb055_wpp_notmem_0033 x) (TEnvFresh.consFresh (nb055_alpha_dummy_004) (nb055_alpha_dummy_005 x y) (nb055_wpp_notmem_0034) (nb055_wpp_notmem_0035 x y) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))

noncomputable def nb055_wpp_refl_0025 (x : Var) (y : Var) : TReflOn [((nb055_alpha_dummy_134), (nb055_alpha_dummy_137 x y)), ((nb055_alpha_dummy_133), (nb055_alpha_dummy_136 x y)), ((nb055_alpha_dummy_132), (nb055_alpha_dummy_135 x y)), ((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)), ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)), ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)), ((nb055_alpha_dummy_152), (nb055_alpha_dummy_153 x y)), ((nb055_alpha_dummy_150), (nb055_alpha_dummy_151 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb055_compact_envfresh_0025 x y)

theorem nb055_wpp_notmem_0362 : (nb055_alpha_dummy_152) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_152, fv_syn_c0] using (nb055_compact_fv_empty_0110)

theorem nb055_wpp_notmem_0363 (x : Var) (y : Var) : (nb055_alpha_dummy_153 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_153, fv_syn_c0] using (nb055_compact_fv_empty_0111 x y)

theorem nb055_wpp_notmem_0364 : (nb055_alpha_dummy_150) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_150, fv_syn_c0] using (nb055_compact_fv_empty_0112)

theorem nb055_wpp_notmem_0365 (x : Var) (y : Var) : (nb055_alpha_dummy_151 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_151, fv_syn_c0] using (nb055_compact_fv_empty_0113 x y)

theorem nb055_wpp_notmem_0366 : (nb055_alpha_dummy_148) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_148, fv_syn_c0] using (nb055_compact_fv_empty_0114)

theorem nb055_wpp_notmem_0367 (x : Var) (y : Var) : (nb055_alpha_dummy_149 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_149, fv_syn_c0] using (nb055_compact_fv_empty_0115 x y)

theorem nb055_compact_envfresh_0026 (x : Var) (y : Var) : TEnvFresh [((nb055_alpha_dummy_134), (nb055_alpha_dummy_137 x y)), ((nb055_alpha_dummy_133), (nb055_alpha_dummy_136 x y)), ((nb055_alpha_dummy_132), (nb055_alpha_dummy_135 x y)), ((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)), ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)), ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)), ((nb055_alpha_dummy_152), (nb055_alpha_dummy_153 x y)), ((nb055_alpha_dummy_150), (nb055_alpha_dummy_151 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb055_alpha_dummy_134) (nb055_alpha_dummy_137 x y) (nb055_wpp_notmem_0318) (nb055_wpp_notmem_0319 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_133) (nb055_alpha_dummy_136 x y) (nb055_wpp_notmem_0320) (nb055_wpp_notmem_0321 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_132) (nb055_alpha_dummy_135 x y) (nb055_wpp_notmem_0322) (nb055_wpp_notmem_0323 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_130) (nb055_alpha_dummy_131 x y) (nb055_wpp_notmem_0324) (nb055_wpp_notmem_0325 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_126) (nb055_alpha_dummy_128 x y) (nb055_wpp_notmem_0326) (nb055_wpp_notmem_0327 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_127) (nb055_alpha_dummy_129 x y) (nb055_wpp_notmem_0328) (nb055_wpp_notmem_0329 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_152) (nb055_alpha_dummy_153 x y) (nb055_wpp_notmem_0362) (nb055_wpp_notmem_0363 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_150) (nb055_alpha_dummy_151 x y) (nb055_wpp_notmem_0364) (nb055_wpp_notmem_0365 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_119) (nb055_alpha_dummy_121 x y) (nb055_wpp_notmem_0330) (nb055_wpp_notmem_0331 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_118) (nb055_alpha_dummy_120 x y) (nb055_wpp_notmem_0332) (nb055_wpp_notmem_0333 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_148) (nb055_alpha_dummy_149 x y) (nb055_wpp_notmem_0366) (nb055_wpp_notmem_0367 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_122) (nb055_alpha_dummy_123 x y) (nb055_wpp_notmem_0336) (nb055_wpp_notmem_0337 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_078) (nb055_alpha_dummy_079 x y) (nb055_wpp_notmem_0338) (nb055_wpp_notmem_0339 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_015) (nb055_alpha_dummy_017 x y) (nb055_wpp_notmem_0048) (nb055_wpp_notmem_0049 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_014) (nb055_alpha_dummy_016 x y) (nb055_wpp_notmem_0050) (nb055_wpp_notmem_0051 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_080) (nb055_alpha_dummy_081 x y) (nb055_wpp_notmem_0248) (nb055_wpp_notmem_0249 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_002) (nb055_alpha_dummy_003 x y) (nb055_wpp_notmem_0064) (nb055_wpp_notmem_0065 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_001) y (nb055_wpp_notmem_0066) (nb055_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb055_alpha_dummy_000) x (nb055_wpp_notmem_0068) (nb055_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb055_alpha_dummy_004) (nb055_alpha_dummy_005 x y) (nb055_wpp_notmem_0070) (nb055_wpp_notmem_0071 x y) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))

noncomputable def nb055_wpp_refl_0026 (x : Var) (y : Var) : TReflOn [((nb055_alpha_dummy_134), (nb055_alpha_dummy_137 x y)), ((nb055_alpha_dummy_133), (nb055_alpha_dummy_136 x y)), ((nb055_alpha_dummy_132), (nb055_alpha_dummy_135 x y)), ((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)), ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)), ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)), ((nb055_alpha_dummy_152), (nb055_alpha_dummy_153 x y)), ((nb055_alpha_dummy_150), (nb055_alpha_dummy_151 x y)), ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)), ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb055_compact_envfresh_0026 x y)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
