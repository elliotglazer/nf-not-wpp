import NAR4C068C001Part017

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

theorem nb068_compact_envfresh_0020 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_121), (nb068_alpha_dummy_122 f)), ((nb068_alpha_dummy_090), (nb068_alpha_dummy_092 f)), ((nb068_alpha_dummy_089), (nb068_alpha_dummy_091 f)), ((nb068_alpha_dummy_119), (nb068_alpha_dummy_120 f)), ((nb068_alpha_dummy_093), (nb068_alpha_dummy_094 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_121) (nb068_alpha_dummy_122 f) (nb068_wpp_notmem_0314) (nb068_wpp_notmem_0315 f) (TEnvFresh.consFresh (nb068_alpha_dummy_090) (nb068_alpha_dummy_092 f) (nb068_wpp_notmem_0316) (nb068_wpp_notmem_0317 f) (TEnvFresh.consFresh (nb068_alpha_dummy_089) (nb068_alpha_dummy_091 f) (nb068_wpp_notmem_0318) (nb068_wpp_notmem_0319 f) (TEnvFresh.consFresh (nb068_alpha_dummy_119) (nb068_alpha_dummy_120 f) (nb068_wpp_notmem_0320) (nb068_wpp_notmem_0321 f) (TEnvFresh.consFresh (nb068_alpha_dummy_093) (nb068_alpha_dummy_094 f) (nb068_wpp_notmem_0322) (nb068_wpp_notmem_0323 f) (TEnvFresh.consFresh (nb068_alpha_dummy_047) (nb068_alpha_dummy_050 f) (nb068_wpp_notmem_0324) (nb068_wpp_notmem_0325 f) (TEnvFresh.consFresh (nb068_alpha_dummy_046) (nb068_alpha_dummy_049 f) (nb068_wpp_notmem_0224) (nb068_wpp_notmem_0225 f) (TEnvFresh.consFresh (nb068_alpha_dummy_045) (nb068_alpha_dummy_048 f) (nb068_wpp_notmem_0226) (nb068_wpp_notmem_0227 f) (TEnvFresh.consFresh (nb068_alpha_dummy_051) (nb068_alpha_dummy_052 f) (nb068_wpp_notmem_0228) (nb068_wpp_notmem_0229 f) (TEnvFresh.consFresh (nb068_alpha_dummy_043) (nb068_alpha_dummy_044 f) (nb068_wpp_notmem_0230) (nb068_wpp_notmem_0231 f) (TEnvFresh.consFresh (nb068_alpha_dummy_041) (nb068_alpha_dummy_042 f) (nb068_wpp_notmem_0232) (nb068_wpp_notmem_0233 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0234) (nb068_wpp_notmem_0235 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0100) (nb068_wpp_notmem_0101 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0102) (nb068_wpp_notmem_0103 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0104) (nb068_wpp_notmem_0105 x y f) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))))

noncomputable def nb068_wpp_refl_0020 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_121), (nb068_alpha_dummy_122 f)), ((nb068_alpha_dummy_090), (nb068_alpha_dummy_092 f)), ((nb068_alpha_dummy_089), (nb068_alpha_dummy_091 f)), ((nb068_alpha_dummy_119), (nb068_alpha_dummy_120 f)), ((nb068_alpha_dummy_093), (nb068_alpha_dummy_094 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0020 x y f)

noncomputable def nb068_split_alpha_0014 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_119), (nb068_alpha_dummy_120 f)), ((nb068_alpha_dummy_093), (nb068_alpha_dummy_094 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_119)) (Class.cab (nb068_alpha_dummy_089) (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_047)) (Wff.classEq (Class.cv (nb068_alpha_dummy_089)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_090))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_119)) (Class.cab (nb068_alpha_dummy_089) (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_047)) (Wff.classEq (Class.cv (nb068_alpha_dummy_089)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_090))) (syn_csn (syn_c0c))))))))) (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_120 f)) (Class.cab (nb068_alpha_dummy_091 f) (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_050 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_120 f)) (Class.cab (nb068_alpha_dummy_091 f) (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_050 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))) (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0112) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0114 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0112) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0114 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0116) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0117 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0113) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0115 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_047))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_050 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0013 x y f))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0013 x y f))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_121), (nb068_alpha_dummy_122 f)), ((nb068_alpha_dummy_090), (nb068_alpha_dummy_092 f)), ((nb068_alpha_dummy_089), (nb068_alpha_dummy_091 f)), ((nb068_alpha_dummy_119), (nb068_alpha_dummy_120 f)), ((nb068_alpha_dummy_093), (nb068_alpha_dummy_094 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_ccompl (syn_csn (syn_c0c))) (nb068_wpp_refl_0020 x y f))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0112) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0114 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0112) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0114 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0116) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0117 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0113) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0115 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_047))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_050 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0013 x y f))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0013 x y f))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_121), (nb068_alpha_dummy_122 f)), ((nb068_alpha_dummy_090), (nb068_alpha_dummy_092 f)), ((nb068_alpha_dummy_089), (nb068_alpha_dummy_091 f)), ((nb068_alpha_dummy_119), (nb068_alpha_dummy_120 f)), ((nb068_alpha_dummy_093), (nb068_alpha_dummy_094 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_ccompl (syn_csn (syn_c0c))) (nb068_wpp_refl_0020 x y f)))))))))))))))))))

theorem nb068_compact_fv_empty_0098 : (nb068_alpha_dummy_147) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0326 : (nb068_alpha_dummy_147) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_147, fv_syn_c1c] using (nb068_compact_fv_empty_0098)

theorem nb068_compact_fv_empty_0099 (f : Var) : (nb068_alpha_dummy_150 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0327 (f : Var) : (nb068_alpha_dummy_150 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_150, fv_syn_c1c] using (nb068_compact_fv_empty_0099 f)

theorem nb068_compact_fv_empty_0100 : (nb068_alpha_dummy_146) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0328 : (nb068_alpha_dummy_146) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_146, fv_syn_c1c] using (nb068_compact_fv_empty_0100)

theorem nb068_compact_fv_empty_0101 (f : Var) : (nb068_alpha_dummy_149 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0329 (f : Var) : (nb068_alpha_dummy_149 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_149, fv_syn_c1c] using (nb068_compact_fv_empty_0101 f)

theorem nb068_compact_fv_empty_0102 : (nb068_alpha_dummy_145) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0330 : (nb068_alpha_dummy_145) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_145, fv_syn_c1c] using (nb068_compact_fv_empty_0102)

theorem nb068_compact_fv_empty_0103 (f : Var) : (nb068_alpha_dummy_148 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0331 (f : Var) : (nb068_alpha_dummy_148 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_148, fv_syn_c1c] using (nb068_compact_fv_empty_0103 f)

theorem nb068_compact_fv_empty_0104 : (nb068_alpha_dummy_143) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0332 : (nb068_alpha_dummy_143) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_143, fv_syn_c1c] using (nb068_compact_fv_empty_0104)

theorem nb068_compact_fv_empty_0105 (f : Var) : (nb068_alpha_dummy_144 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0333 (f : Var) : (nb068_alpha_dummy_144 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_144, fv_syn_c1c] using (nb068_compact_fv_empty_0105 f)

theorem nb068_compact_fv_empty_0106 : (nb068_alpha_dummy_139) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0334 : (nb068_alpha_dummy_139) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_139, fv_syn_c1c] using (nb068_compact_fv_empty_0106)

theorem nb068_compact_fv_empty_0107 (f : Var) : (nb068_alpha_dummy_141 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0335 (f : Var) : (nb068_alpha_dummy_141 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_141, fv_syn_c1c] using (nb068_compact_fv_empty_0107 f)

theorem nb068_compact_fv_empty_0108 : (nb068_alpha_dummy_140) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0336 : (nb068_alpha_dummy_140) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_140, fv_syn_c1c] using (nb068_compact_fv_empty_0108)

theorem nb068_compact_fv_empty_0109 (f : Var) : (nb068_alpha_dummy_142 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0337 (f : Var) : (nb068_alpha_dummy_142 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_142, fv_syn_c1c] using (nb068_compact_fv_empty_0109 f)

theorem nb068_compact_fv_empty_0110 : (nb068_alpha_dummy_132) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0338 : (nb068_alpha_dummy_132) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_132, fv_syn_c1c] using (nb068_compact_fv_empty_0110)

theorem nb068_compact_fv_empty_0111 (f : Var) : (nb068_alpha_dummy_134 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0339 (f : Var) : (nb068_alpha_dummy_134 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_134, fv_syn_c1c] using (nb068_compact_fv_empty_0111 f)

theorem nb068_compact_fv_empty_0112 : (nb068_alpha_dummy_131) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0340 : (nb068_alpha_dummy_131) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_131, fv_syn_c1c] using (nb068_compact_fv_empty_0112)

theorem nb068_compact_fv_empty_0113 (f : Var) : (nb068_alpha_dummy_133 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0341 (f : Var) : (nb068_alpha_dummy_133 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_133, fv_syn_c1c] using (nb068_compact_fv_empty_0113 f)

theorem nb068_compact_fv_empty_0114 : (nb068_alpha_dummy_137) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0342 : (nb068_alpha_dummy_137) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_137, fv_syn_c1c] using (nb068_compact_fv_empty_0114)

theorem nb068_compact_fv_empty_0115 (f : Var) : (nb068_alpha_dummy_138 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0343 (f : Var) : (nb068_alpha_dummy_138 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_138, fv_syn_c1c] using (nb068_compact_fv_empty_0115 f)

theorem nb068_compact_fv_empty_0116 : (nb068_alpha_dummy_135) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0344 : (nb068_alpha_dummy_135) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_135, fv_syn_c1c] using (nb068_compact_fv_empty_0116)

theorem nb068_compact_fv_empty_0117 (f : Var) : (nb068_alpha_dummy_136 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0345 (f : Var) : (nb068_alpha_dummy_136 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_136, fv_syn_c1c] using (nb068_compact_fv_empty_0117 f)

theorem nb068_compact_fv_empty_0118 : (nb068_alpha_dummy_126) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0346 : (nb068_alpha_dummy_126) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_126, fv_syn_c1c] using (nb068_compact_fv_empty_0118)

theorem nb068_compact_fv_empty_0119 (f : Var) : (nb068_alpha_dummy_128 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0347 (f : Var) : (nb068_alpha_dummy_128 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_128, fv_syn_c1c] using (nb068_compact_fv_empty_0119 f)

theorem nb068_compact_fv_empty_0120 : (nb068_alpha_dummy_125) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0348 : (nb068_alpha_dummy_125) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_125, fv_syn_c1c] using (nb068_compact_fv_empty_0120)

theorem nb068_compact_fv_empty_0121 (f : Var) : (nb068_alpha_dummy_127 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0349 (f : Var) : (nb068_alpha_dummy_127 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_127, fv_syn_c1c] using (nb068_compact_fv_empty_0121 f)

theorem nb068_compact_fv_empty_0122 : (nb068_alpha_dummy_129) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0350 : (nb068_alpha_dummy_129) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_129, fv_syn_c1c] using (nb068_compact_fv_empty_0122)

theorem nb068_compact_fv_empty_0123 (f : Var) : (nb068_alpha_dummy_130 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0351 (f : Var) : (nb068_alpha_dummy_130 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_130, fv_syn_c1c] using (nb068_compact_fv_empty_0123 f)

theorem nb068_compact_envfresh_0021 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_147), (nb068_alpha_dummy_150 f)), ((nb068_alpha_dummy_146), (nb068_alpha_dummy_149 f)), ((nb068_alpha_dummy_145), (nb068_alpha_dummy_148 f)), ((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)), ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)), ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)), ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)), ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)), ((nb068_alpha_dummy_137), (nb068_alpha_dummy_138 f)), ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)), ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)), ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)), ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_147) (nb068_alpha_dummy_150 f) (nb068_wpp_notmem_0326) (nb068_wpp_notmem_0327 f) (TEnvFresh.consFresh (nb068_alpha_dummy_146) (nb068_alpha_dummy_149 f) (nb068_wpp_notmem_0328) (nb068_wpp_notmem_0329 f) (TEnvFresh.consFresh (nb068_alpha_dummy_145) (nb068_alpha_dummy_148 f) (nb068_wpp_notmem_0330) (nb068_wpp_notmem_0331 f) (TEnvFresh.consFresh (nb068_alpha_dummy_143) (nb068_alpha_dummy_144 f) (nb068_wpp_notmem_0332) (nb068_wpp_notmem_0333 f) (TEnvFresh.consFresh (nb068_alpha_dummy_139) (nb068_alpha_dummy_141 f) (nb068_wpp_notmem_0334) (nb068_wpp_notmem_0335 f) (TEnvFresh.consFresh (nb068_alpha_dummy_140) (nb068_alpha_dummy_142 f) (nb068_wpp_notmem_0336) (nb068_wpp_notmem_0337 f) (TEnvFresh.consFresh (nb068_alpha_dummy_132) (nb068_alpha_dummy_134 f) (nb068_wpp_notmem_0338) (nb068_wpp_notmem_0339 f) (TEnvFresh.consFresh (nb068_alpha_dummy_131) (nb068_alpha_dummy_133 f) (nb068_wpp_notmem_0340) (nb068_wpp_notmem_0341 f) (TEnvFresh.consFresh (nb068_alpha_dummy_137) (nb068_alpha_dummy_138 f) (nb068_wpp_notmem_0342) (nb068_wpp_notmem_0343 f) (TEnvFresh.consFresh (nb068_alpha_dummy_135) (nb068_alpha_dummy_136 f) (nb068_wpp_notmem_0344) (nb068_wpp_notmem_0345 f) (TEnvFresh.consFresh (nb068_alpha_dummy_126) (nb068_alpha_dummy_128 f) (nb068_wpp_notmem_0346) (nb068_wpp_notmem_0347 f) (TEnvFresh.consFresh (nb068_alpha_dummy_125) (nb068_alpha_dummy_127 f) (nb068_wpp_notmem_0348) (nb068_wpp_notmem_0349 f) (TEnvFresh.consFresh (nb068_alpha_dummy_129) (nb068_alpha_dummy_130 f) (nb068_wpp_notmem_0350) (nb068_wpp_notmem_0351 f) (TEnvFresh.consFresh (nb068_alpha_dummy_047) (nb068_alpha_dummy_050 f) (nb068_wpp_notmem_0256) (nb068_wpp_notmem_0257 f) (TEnvFresh.consFresh (nb068_alpha_dummy_046) (nb068_alpha_dummy_049 f) (nb068_wpp_notmem_0126) (nb068_wpp_notmem_0127 f) (TEnvFresh.consFresh (nb068_alpha_dummy_045) (nb068_alpha_dummy_048 f) (nb068_wpp_notmem_0128) (nb068_wpp_notmem_0129 f) (TEnvFresh.consFresh (nb068_alpha_dummy_051) (nb068_alpha_dummy_052 f) (nb068_wpp_notmem_0130) (nb068_wpp_notmem_0131 f) (TEnvFresh.consFresh (nb068_alpha_dummy_043) (nb068_alpha_dummy_044 f) (nb068_wpp_notmem_0132) (nb068_wpp_notmem_0133 f) (TEnvFresh.consFresh (nb068_alpha_dummy_041) (nb068_alpha_dummy_042 f) (nb068_wpp_notmem_0134) (nb068_wpp_notmem_0135 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0136) (nb068_wpp_notmem_0137 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0020) (nb068_wpp_notmem_0021 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0022) (nb068_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0024) (nb068_wpp_notmem_0025 x y f) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))))))

noncomputable def nb068_wpp_refl_0021 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_147), (nb068_alpha_dummy_150 f)), ((nb068_alpha_dummy_146), (nb068_alpha_dummy_149 f)), ((nb068_alpha_dummy_145), (nb068_alpha_dummy_148 f)), ((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)), ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)), ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)), ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)), ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)), ((nb068_alpha_dummy_137), (nb068_alpha_dummy_138 f)), ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)), ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)), ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)), ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0021 x y f)

theorem nb068_wpp_notmem_0352 : (nb068_alpha_dummy_147) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_147, fv_syn_c0] using (nb068_compact_fv_empty_0098)

theorem nb068_wpp_notmem_0353 (f : Var) : (nb068_alpha_dummy_150 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_150, fv_syn_c0] using (nb068_compact_fv_empty_0099 f)

theorem nb068_wpp_notmem_0354 : (nb068_alpha_dummy_146) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_146, fv_syn_c0] using (nb068_compact_fv_empty_0100)

theorem nb068_wpp_notmem_0355 (f : Var) : (nb068_alpha_dummy_149 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_149, fv_syn_c0] using (nb068_compact_fv_empty_0101 f)

theorem nb068_wpp_notmem_0356 : (nb068_alpha_dummy_145) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_145, fv_syn_c0] using (nb068_compact_fv_empty_0102)

theorem nb068_wpp_notmem_0357 (f : Var) : (nb068_alpha_dummy_148 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_148, fv_syn_c0] using (nb068_compact_fv_empty_0103 f)

theorem nb068_wpp_notmem_0358 : (nb068_alpha_dummy_143) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_143, fv_syn_c0] using (nb068_compact_fv_empty_0104)

theorem nb068_wpp_notmem_0359 (f : Var) : (nb068_alpha_dummy_144 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_144, fv_syn_c0] using (nb068_compact_fv_empty_0105 f)

theorem nb068_wpp_notmem_0360 : (nb068_alpha_dummy_139) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_139, fv_syn_c0] using (nb068_compact_fv_empty_0106)

theorem nb068_wpp_notmem_0361 (f : Var) : (nb068_alpha_dummy_141 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_141, fv_syn_c0] using (nb068_compact_fv_empty_0107 f)

theorem nb068_wpp_notmem_0362 : (nb068_alpha_dummy_140) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_140, fv_syn_c0] using (nb068_compact_fv_empty_0108)

theorem nb068_wpp_notmem_0363 (f : Var) : (nb068_alpha_dummy_142 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_142, fv_syn_c0] using (nb068_compact_fv_empty_0109 f)

theorem nb068_wpp_notmem_0364 : (nb068_alpha_dummy_132) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_132, fv_syn_c0] using (nb068_compact_fv_empty_0110)

theorem nb068_wpp_notmem_0365 (f : Var) : (nb068_alpha_dummy_134 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_134, fv_syn_c0] using (nb068_compact_fv_empty_0111 f)

theorem nb068_wpp_notmem_0366 : (nb068_alpha_dummy_131) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_131, fv_syn_c0] using (nb068_compact_fv_empty_0112)

theorem nb068_wpp_notmem_0367 (f : Var) : (nb068_alpha_dummy_133 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_133, fv_syn_c0] using (nb068_compact_fv_empty_0113 f)

theorem nb068_wpp_notmem_0368 : (nb068_alpha_dummy_137) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_137, fv_syn_c0] using (nb068_compact_fv_empty_0114)

theorem nb068_wpp_notmem_0369 (f : Var) : (nb068_alpha_dummy_138 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_138, fv_syn_c0] using (nb068_compact_fv_empty_0115 f)

theorem nb068_wpp_notmem_0370 : (nb068_alpha_dummy_135) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_135, fv_syn_c0] using (nb068_compact_fv_empty_0116)

theorem nb068_wpp_notmem_0371 (f : Var) : (nb068_alpha_dummy_136 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_136, fv_syn_c0] using (nb068_compact_fv_empty_0117 f)

theorem nb068_wpp_notmem_0372 : (nb068_alpha_dummy_126) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_126, fv_syn_c0] using (nb068_compact_fv_empty_0118)

theorem nb068_wpp_notmem_0373 (f : Var) : (nb068_alpha_dummy_128 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_128, fv_syn_c0] using (nb068_compact_fv_empty_0119 f)

theorem nb068_wpp_notmem_0374 : (nb068_alpha_dummy_125) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_125, fv_syn_c0] using (nb068_compact_fv_empty_0120)

theorem nb068_wpp_notmem_0375 (f : Var) : (nb068_alpha_dummy_127 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_127, fv_syn_c0] using (nb068_compact_fv_empty_0121 f)

theorem nb068_wpp_notmem_0376 : (nb068_alpha_dummy_129) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_129, fv_syn_c0] using (nb068_compact_fv_empty_0122)

theorem nb068_wpp_notmem_0377 (f : Var) : (nb068_alpha_dummy_130 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_130, fv_syn_c0] using (nb068_compact_fv_empty_0123 f)

theorem nb068_compact_envfresh_0022 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_147), (nb068_alpha_dummy_150 f)), ((nb068_alpha_dummy_146), (nb068_alpha_dummy_149 f)), ((nb068_alpha_dummy_145), (nb068_alpha_dummy_148 f)), ((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)), ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)), ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)), ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)), ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)), ((nb068_alpha_dummy_137), (nb068_alpha_dummy_138 f)), ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)), ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)), ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)), ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_147) (nb068_alpha_dummy_150 f) (nb068_wpp_notmem_0352) (nb068_wpp_notmem_0353 f) (TEnvFresh.consFresh (nb068_alpha_dummy_146) (nb068_alpha_dummy_149 f) (nb068_wpp_notmem_0354) (nb068_wpp_notmem_0355 f) (TEnvFresh.consFresh (nb068_alpha_dummy_145) (nb068_alpha_dummy_148 f) (nb068_wpp_notmem_0356) (nb068_wpp_notmem_0357 f) (TEnvFresh.consFresh (nb068_alpha_dummy_143) (nb068_alpha_dummy_144 f) (nb068_wpp_notmem_0358) (nb068_wpp_notmem_0359 f) (TEnvFresh.consFresh (nb068_alpha_dummy_139) (nb068_alpha_dummy_141 f) (nb068_wpp_notmem_0360) (nb068_wpp_notmem_0361 f) (TEnvFresh.consFresh (nb068_alpha_dummy_140) (nb068_alpha_dummy_142 f) (nb068_wpp_notmem_0362) (nb068_wpp_notmem_0363 f) (TEnvFresh.consFresh (nb068_alpha_dummy_132) (nb068_alpha_dummy_134 f) (nb068_wpp_notmem_0364) (nb068_wpp_notmem_0365 f) (TEnvFresh.consFresh (nb068_alpha_dummy_131) (nb068_alpha_dummy_133 f) (nb068_wpp_notmem_0366) (nb068_wpp_notmem_0367 f) (TEnvFresh.consFresh (nb068_alpha_dummy_137) (nb068_alpha_dummy_138 f) (nb068_wpp_notmem_0368) (nb068_wpp_notmem_0369 f) (TEnvFresh.consFresh (nb068_alpha_dummy_135) (nb068_alpha_dummy_136 f) (nb068_wpp_notmem_0370) (nb068_wpp_notmem_0371 f) (TEnvFresh.consFresh (nb068_alpha_dummy_126) (nb068_alpha_dummy_128 f) (nb068_wpp_notmem_0372) (nb068_wpp_notmem_0373 f) (TEnvFresh.consFresh (nb068_alpha_dummy_125) (nb068_alpha_dummy_127 f) (nb068_wpp_notmem_0374) (nb068_wpp_notmem_0375 f) (TEnvFresh.consFresh (nb068_alpha_dummy_129) (nb068_alpha_dummy_130 f) (nb068_wpp_notmem_0376) (nb068_wpp_notmem_0377 f) (TEnvFresh.consFresh (nb068_alpha_dummy_047) (nb068_alpha_dummy_050 f) (nb068_wpp_notmem_0278) (nb068_wpp_notmem_0279 f) (TEnvFresh.consFresh (nb068_alpha_dummy_046) (nb068_alpha_dummy_049 f) (nb068_wpp_notmem_0158) (nb068_wpp_notmem_0159 f) (TEnvFresh.consFresh (nb068_alpha_dummy_045) (nb068_alpha_dummy_048 f) (nb068_wpp_notmem_0160) (nb068_wpp_notmem_0161 f) (TEnvFresh.consFresh (nb068_alpha_dummy_051) (nb068_alpha_dummy_052 f) (nb068_wpp_notmem_0162) (nb068_wpp_notmem_0163 f) (TEnvFresh.consFresh (nb068_alpha_dummy_043) (nb068_alpha_dummy_044 f) (nb068_wpp_notmem_0164) (nb068_wpp_notmem_0165 f) (TEnvFresh.consFresh (nb068_alpha_dummy_041) (nb068_alpha_dummy_042 f) (nb068_wpp_notmem_0166) (nb068_wpp_notmem_0167 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0168) (nb068_wpp_notmem_0169 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0046) (nb068_wpp_notmem_0047 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0048) (nb068_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0050) (nb068_wpp_notmem_0051 x y f) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))))))

noncomputable def nb068_wpp_refl_0022 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_147), (nb068_alpha_dummy_150 f)), ((nb068_alpha_dummy_146), (nb068_alpha_dummy_149 f)), ((nb068_alpha_dummy_145), (nb068_alpha_dummy_148 f)), ((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)), ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)), ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)), ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)), ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)), ((nb068_alpha_dummy_137), (nb068_alpha_dummy_138 f)), ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)), ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)), ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)), ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0022 x y f)

noncomputable def nb068_split_alpha_0015 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_147), (nb068_alpha_dummy_150 f)), ((nb068_alpha_dummy_146), (nb068_alpha_dummy_149 f)), ((nb068_alpha_dummy_145), (nb068_alpha_dummy_148 f)), ((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)), ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)), ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)), ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)), ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)), ((nb068_alpha_dummy_137), (nb068_alpha_dummy_138 f)), ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)), ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)), ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)), ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_146)) (Class.cv (nb068_alpha_dummy_147))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_145)) (syn_cun (Class.cv (nb068_alpha_dummy_146)) (Class.cv (nb068_alpha_dummy_147)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_149 f)) (Class.cv (nb068_alpha_dummy_150 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_148 f)) (syn_cun (Class.cv (nb068_alpha_dummy_149 f)) (Class.cv (nb068_alpha_dummy_150 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0140) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0141 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0138) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0139 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0144) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0145 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0142) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0143 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0140) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0141 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0138) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0139 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0144) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0145 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0142) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0143 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_147), (nb068_alpha_dummy_150 f)), ((nb068_alpha_dummy_146), (nb068_alpha_dummy_149 f)), ((nb068_alpha_dummy_145), (nb068_alpha_dummy_148 f)), ((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)), ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)), ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)), ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)), ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)), ((nb068_alpha_dummy_137), (nb068_alpha_dummy_138 f)), ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)), ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)), ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)), ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c0) (nb068_wpp_refl_0022 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0148) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0149 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0147 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0148) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0149 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0147 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0152) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0153 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0150) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0151 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0152) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0153 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0150) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0151 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb068_wpp_notmem_0378 : (nb068_alpha_dummy_143) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_143, fv_syn_cnnc] using (nb068_compact_fv_empty_0104)

theorem nb068_wpp_notmem_0379 (f : Var) : (nb068_alpha_dummy_144 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_144, fv_syn_cnnc] using (nb068_compact_fv_empty_0105 f)

theorem nb068_wpp_notmem_0380 : (nb068_alpha_dummy_139) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_139, fv_syn_cnnc] using (nb068_compact_fv_empty_0106)

theorem nb068_wpp_notmem_0381 (f : Var) : (nb068_alpha_dummy_141 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_141, fv_syn_cnnc] using (nb068_compact_fv_empty_0107 f)

theorem nb068_wpp_notmem_0382 : (nb068_alpha_dummy_140) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_140, fv_syn_cnnc] using (nb068_compact_fv_empty_0108)

theorem nb068_wpp_notmem_0383 (f : Var) : (nb068_alpha_dummy_142 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_142, fv_syn_cnnc] using (nb068_compact_fv_empty_0109 f)

theorem nb068_wpp_notmem_0384 : (nb068_alpha_dummy_132) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_132, fv_syn_cnnc] using (nb068_compact_fv_empty_0110)

theorem nb068_wpp_notmem_0385 (f : Var) : (nb068_alpha_dummy_134 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_134, fv_syn_cnnc] using (nb068_compact_fv_empty_0111 f)

theorem nb068_wpp_notmem_0386 : (nb068_alpha_dummy_131) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_131, fv_syn_cnnc] using (nb068_compact_fv_empty_0112)

theorem nb068_wpp_notmem_0387 (f : Var) : (nb068_alpha_dummy_133 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_133, fv_syn_cnnc] using (nb068_compact_fv_empty_0113 f)

theorem nb068_wpp_notmem_0388 : (nb068_alpha_dummy_137) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_137, fv_syn_cnnc] using (nb068_compact_fv_empty_0114)

theorem nb068_wpp_notmem_0389 (f : Var) : (nb068_alpha_dummy_138 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_138, fv_syn_cnnc] using (nb068_compact_fv_empty_0115 f)

theorem nb068_wpp_notmem_0390 : (nb068_alpha_dummy_135) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_135, fv_syn_cnnc] using (nb068_compact_fv_empty_0116)

theorem nb068_wpp_notmem_0391 (f : Var) : (nb068_alpha_dummy_136 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_136, fv_syn_cnnc] using (nb068_compact_fv_empty_0117 f)

theorem nb068_wpp_notmem_0392 : (nb068_alpha_dummy_126) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_126, fv_syn_cnnc] using (nb068_compact_fv_empty_0118)

theorem nb068_wpp_notmem_0393 (f : Var) : (nb068_alpha_dummy_128 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_128, fv_syn_cnnc] using (nb068_compact_fv_empty_0119 f)

theorem nb068_wpp_notmem_0394 : (nb068_alpha_dummy_125) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_125, fv_syn_cnnc] using (nb068_compact_fv_empty_0120)

theorem nb068_wpp_notmem_0395 (f : Var) : (nb068_alpha_dummy_127 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_127, fv_syn_cnnc] using (nb068_compact_fv_empty_0121 f)

theorem nb068_wpp_notmem_0396 : (nb068_alpha_dummy_129) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_129, fv_syn_cnnc] using (nb068_compact_fv_empty_0122)

theorem nb068_wpp_notmem_0397 (f : Var) : (nb068_alpha_dummy_130 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_130, fv_syn_cnnc] using (nb068_compact_fv_empty_0123 f)

theorem nb068_compact_envfresh_0023 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)), ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)), ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)), ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)), ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)), ((nb068_alpha_dummy_137), (nb068_alpha_dummy_138 f)), ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)), ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)), ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)), ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_143) (nb068_alpha_dummy_144 f) (nb068_wpp_notmem_0378) (nb068_wpp_notmem_0379 f) (TEnvFresh.consFresh (nb068_alpha_dummy_139) (nb068_alpha_dummy_141 f) (nb068_wpp_notmem_0380) (nb068_wpp_notmem_0381 f) (TEnvFresh.consFresh (nb068_alpha_dummy_140) (nb068_alpha_dummy_142 f) (nb068_wpp_notmem_0382) (nb068_wpp_notmem_0383 f) (TEnvFresh.consFresh (nb068_alpha_dummy_132) (nb068_alpha_dummy_134 f) (nb068_wpp_notmem_0384) (nb068_wpp_notmem_0385 f) (TEnvFresh.consFresh (nb068_alpha_dummy_131) (nb068_alpha_dummy_133 f) (nb068_wpp_notmem_0386) (nb068_wpp_notmem_0387 f) (TEnvFresh.consFresh (nb068_alpha_dummy_137) (nb068_alpha_dummy_138 f) (nb068_wpp_notmem_0388) (nb068_wpp_notmem_0389 f) (TEnvFresh.consFresh (nb068_alpha_dummy_135) (nb068_alpha_dummy_136 f) (nb068_wpp_notmem_0390) (nb068_wpp_notmem_0391 f) (TEnvFresh.consFresh (nb068_alpha_dummy_126) (nb068_alpha_dummy_128 f) (nb068_wpp_notmem_0392) (nb068_wpp_notmem_0393 f) (TEnvFresh.consFresh (nb068_alpha_dummy_125) (nb068_alpha_dummy_127 f) (nb068_wpp_notmem_0394) (nb068_wpp_notmem_0395 f) (TEnvFresh.consFresh (nb068_alpha_dummy_129) (nb068_alpha_dummy_130 f) (nb068_wpp_notmem_0396) (nb068_wpp_notmem_0397 f) (TEnvFresh.consFresh (nb068_alpha_dummy_047) (nb068_alpha_dummy_050 f) (nb068_wpp_notmem_0294) (nb068_wpp_notmem_0295 f) (TEnvFresh.consFresh (nb068_alpha_dummy_046) (nb068_alpha_dummy_049 f) (nb068_wpp_notmem_0184) (nb068_wpp_notmem_0185 f) (TEnvFresh.consFresh (nb068_alpha_dummy_045) (nb068_alpha_dummy_048 f) (nb068_wpp_notmem_0186) (nb068_wpp_notmem_0187 f) (TEnvFresh.consFresh (nb068_alpha_dummy_051) (nb068_alpha_dummy_052 f) (nb068_wpp_notmem_0188) (nb068_wpp_notmem_0189 f) (TEnvFresh.consFresh (nb068_alpha_dummy_043) (nb068_alpha_dummy_044 f) (nb068_wpp_notmem_0190) (nb068_wpp_notmem_0191 f) (TEnvFresh.consFresh (nb068_alpha_dummy_041) (nb068_alpha_dummy_042 f) (nb068_wpp_notmem_0192) (nb068_wpp_notmem_0193 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0194) (nb068_wpp_notmem_0195 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0066) (nb068_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0068) (nb068_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0070) (nb068_wpp_notmem_0071 x y f) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))))))

noncomputable def nb068_wpp_refl_0023 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)), ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)), ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)), ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)), ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)), ((nb068_alpha_dummy_137), (nb068_alpha_dummy_138 f)), ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)), ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)), ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)), ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0023 x y f)

noncomputable def nb068_split_alpha_0016 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)), ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)), ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)), ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)), ((nb068_alpha_dummy_137), (nb068_alpha_dummy_138 f)), ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)), ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)), ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)), ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.classEq (Class.cv (nb068_alpha_dummy_140)) (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_139)) (syn_cnnc)) (syn_cplc (Class.cv (nb068_alpha_dummy_139)) (syn_c1c)) (Class.cv (nb068_alpha_dummy_139)))) (Wff.classEq (Class.cv (nb068_alpha_dummy_142 f)) (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_141 f)) (syn_cnnc)) (syn_cplc (Class.cv (nb068_alpha_dummy_141 f)) (syn_c1c)) (Class.cv (nb068_alpha_dummy_141 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_132))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_134 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0136) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0137 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0136) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0137 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_147), (nb068_alpha_dummy_150 f)), ((nb068_alpha_dummy_146), (nb068_alpha_dummy_149 f)), ((nb068_alpha_dummy_145), (nb068_alpha_dummy_148 f)), ((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)), ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)), ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)), ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)), ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)), ((nb068_alpha_dummy_137), (nb068_alpha_dummy_138 f)), ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)), ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)), ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)), ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c1c) (nb068_wpp_refl_0021 x y f))) (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0015 x y f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)), ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)), ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)), ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)), ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)), ((nb068_alpha_dummy_137), (nb068_alpha_dummy_138 f)), ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)), ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)), ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)), ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0023 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)), ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)), ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)), ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)), ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)), ((nb068_alpha_dummy_137), (nb068_alpha_dummy_138 f)), ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)), ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)), ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)), ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0023 x y f))))))))))

theorem nb068_compact_fv_empty_0124 : (nb068_alpha_dummy_165) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0398 : (nb068_alpha_dummy_165) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_165, fv_syn_c1c] using (nb068_compact_fv_empty_0124)

theorem nb068_compact_fv_empty_0125 (f : Var) : (nb068_alpha_dummy_166 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0399 (f : Var) : (nb068_alpha_dummy_166 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_166, fv_syn_c1c] using (nb068_compact_fv_empty_0125 f)

theorem nb068_compact_fv_empty_0126 : (nb068_alpha_dummy_163) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0400 : (nb068_alpha_dummy_163) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_163, fv_syn_c1c] using (nb068_compact_fv_empty_0126)

theorem nb068_compact_fv_empty_0127 (f : Var) : (nb068_alpha_dummy_164 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0401 (f : Var) : (nb068_alpha_dummy_164 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_164, fv_syn_c1c] using (nb068_compact_fv_empty_0127 f)

theorem nb068_compact_fv_empty_0128 : (nb068_alpha_dummy_161) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0402 : (nb068_alpha_dummy_161) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_161, fv_syn_c1c] using (nb068_compact_fv_empty_0128)

theorem nb068_compact_fv_empty_0129 (f : Var) : (nb068_alpha_dummy_162 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0403 (f : Var) : (nb068_alpha_dummy_162 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_162, fv_syn_c1c] using (nb068_compact_fv_empty_0129 f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
