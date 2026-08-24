import NAR4C067C001Part013

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

noncomputable def nb067_split_alpha_0013 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)), ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)), ((nb067_alpha_dummy_125), (nb067_alpha_dummy_126 f)), ((nb067_alpha_dummy_123), (nb067_alpha_dummy_124 f)), ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)), ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)), ((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)), ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_099)) (Class.cv (nb067_alpha_dummy_092))) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_100)) (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_099)) (syn_cnnc)) (syn_cplc (Class.cv (nb067_alpha_dummy_099)) (syn_c1c)) (Class.cv (nb067_alpha_dummy_099)))))) (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_101 f)) (Class.cv (nb067_alpha_dummy_094 f))) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_102 f)) (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_101 f)) (syn_cnnc)) (syn_cplc (Class.cv (nb067_alpha_dummy_101 f)) (syn_c1c)) (Class.cv (nb067_alpha_dummy_101 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0102) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0103 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0102) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0103 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0132) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0133 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0130) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0131 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_092))).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_094 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0106) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0107 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0107 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0105 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_107), (nb067_alpha_dummy_110 f)), ((nb067_alpha_dummy_106), (nb067_alpha_dummy_109 f)), ((nb067_alpha_dummy_105), (nb067_alpha_dummy_108 f)), ((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)), ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)), ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)), ((nb067_alpha_dummy_125), (nb067_alpha_dummy_126 f)), ((nb067_alpha_dummy_123), (nb067_alpha_dummy_124 f)), ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)), ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)), ((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)), ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_c1c) (nb067_wpp_refl_0018 x y f))) (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0012 x y f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0105 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)), ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)), ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)), ((nb067_alpha_dummy_125), (nb067_alpha_dummy_126 f)), ((nb067_alpha_dummy_123), (nb067_alpha_dummy_124 f)), ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)), ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)), ((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)), ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_cnnc) (nb067_wpp_refl_0020 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0105 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0105 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)), ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)), ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)), ((nb067_alpha_dummy_125), (nb067_alpha_dummy_126 f)), ((nb067_alpha_dummy_123), (nb067_alpha_dummy_124 f)), ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)), ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)), ((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)), ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_cnnc) (nb067_wpp_refl_0020 x y f))))))))))))

theorem nb067_wpp_notmem_0314 : (nb067_alpha_dummy_123) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_123, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0094)

theorem nb067_wpp_notmem_0315 (f : Var) : (nb067_alpha_dummy_124 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_124, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0095 f)

theorem nb067_wpp_notmem_0316 : (nb067_alpha_dummy_092) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_092, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0072)

theorem nb067_wpp_notmem_0317 (f : Var) : (nb067_alpha_dummy_094 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_094, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0073 f)

theorem nb067_wpp_notmem_0318 : (nb067_alpha_dummy_091) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_091, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0074)

theorem nb067_wpp_notmem_0319 (f : Var) : (nb067_alpha_dummy_093 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_093, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0075 f)

theorem nb067_wpp_notmem_0320 : (nb067_alpha_dummy_121) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_121, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0096)

theorem nb067_wpp_notmem_0321 (f : Var) : (nb067_alpha_dummy_122 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_122, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0097 f)

theorem nb067_wpp_notmem_0322 : (nb067_alpha_dummy_095) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_095, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0078)

theorem nb067_wpp_notmem_0323 (f : Var) : (nb067_alpha_dummy_096 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_096, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0079 f)

theorem nb067_wpp_notmem_0324 : (nb067_alpha_dummy_084) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_084, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0080)

theorem nb067_wpp_notmem_0325 (f : Var) : (nb067_alpha_dummy_087 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_087, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0081 f)

theorem nb067_wpp_notmem_0326 : (nb067_alpha_dummy_083) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_083, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0082)

theorem nb067_wpp_notmem_0327 (f : Var) : (nb067_alpha_dummy_086 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_086, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0083 f)

theorem nb067_wpp_notmem_0328 : (nb067_alpha_dummy_089) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_089, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0084)

theorem nb067_wpp_notmem_0329 (f : Var) : (nb067_alpha_dummy_090 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_090, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0085 f)

theorem nb067_wpp_notmem_0330 : (nb067_alpha_dummy_081) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_081, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0086)

theorem nb067_wpp_notmem_0331 (f : Var) : (nb067_alpha_dummy_082 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_082, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0087 f)

theorem nb067_wpp_notmem_0332 : (nb067_alpha_dummy_079) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_079, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0088)

theorem nb067_wpp_notmem_0333 (f : Var) : (nb067_alpha_dummy_080 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_080, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0089 f)

theorem nb067_wpp_notmem_0334 : (nb067_alpha_dummy_000) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_000, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0090)

theorem nb067_wpp_notmem_0335 (f : Var) : f ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0091 f)

theorem nb067_compact_envfresh_0021 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_123), (nb067_alpha_dummy_124 f)), ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)), ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)), ((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)), ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_123) (nb067_alpha_dummy_124 f) (nb067_wpp_notmem_0314) (nb067_wpp_notmem_0315 f) (TEnvFresh.consFresh (nb067_alpha_dummy_092) (nb067_alpha_dummy_094 f) (nb067_wpp_notmem_0316) (nb067_wpp_notmem_0317 f) (TEnvFresh.consFresh (nb067_alpha_dummy_091) (nb067_alpha_dummy_093 f) (nb067_wpp_notmem_0318) (nb067_wpp_notmem_0319 f) (TEnvFresh.consFresh (nb067_alpha_dummy_121) (nb067_alpha_dummy_122 f) (nb067_wpp_notmem_0320) (nb067_wpp_notmem_0321 f) (TEnvFresh.consFresh (nb067_alpha_dummy_095) (nb067_alpha_dummy_096 f) (nb067_wpp_notmem_0322) (nb067_wpp_notmem_0323 f) (TEnvFresh.consFresh (nb067_alpha_dummy_084) (nb067_alpha_dummy_087 f) (nb067_wpp_notmem_0324) (nb067_wpp_notmem_0325 f) (TEnvFresh.consFresh (nb067_alpha_dummy_083) (nb067_alpha_dummy_086 f) (nb067_wpp_notmem_0326) (nb067_wpp_notmem_0327 f) (TEnvFresh.consFresh (nb067_alpha_dummy_089) (nb067_alpha_dummy_090 f) (nb067_wpp_notmem_0328) (nb067_wpp_notmem_0329 f) (TEnvFresh.consFresh (nb067_alpha_dummy_081) (nb067_alpha_dummy_082 f) (nb067_wpp_notmem_0330) (nb067_wpp_notmem_0331 f) (TEnvFresh.consFresh (nb067_alpha_dummy_079) (nb067_alpha_dummy_080 f) (nb067_wpp_notmem_0332) (nb067_wpp_notmem_0333 f) (TEnvFresh.consFresh (nb067_alpha_dummy_000) f (nb067_wpp_notmem_0334) (nb067_wpp_notmem_0335 f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0138) (nb067_wpp_notmem_0139 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0140) (nb067_wpp_notmem_0141 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0142) (nb067_wpp_notmem_0143 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0144) (nb067_wpp_notmem_0145 x y f) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))))

noncomputable def nb067_wpp_refl_0021 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_123), (nb067_alpha_dummy_124 f)), ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)), ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)), ((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)), ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0021 x y f)

noncomputable def nb067_split_alpha_0014 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)), ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_121)) (Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_121)) (Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092))) (syn_csn (syn_c0c))))))))) (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_122 f)) (Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_122 f)) (Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))) (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0126 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0126 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0128) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0129 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0125) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0127 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0013 x y f))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0013 x y f))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_123), (nb067_alpha_dummy_124 f)), ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)), ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)), ((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)), ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_ccompl (syn_csn (syn_c0c))) (nb067_wpp_refl_0021 x y f))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0126 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0126 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0128) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0129 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0125) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0127 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0013 x y f))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0013 x y f))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_123), (nb067_alpha_dummy_124 f)), ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)), ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)), ((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)), ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_ccompl (syn_csn (syn_c0c))) (nb067_wpp_refl_0021 x y f)))))))))))))))))))

theorem nb067_compact_fv_empty_0098 : (nb067_alpha_dummy_143) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0336 : (nb067_alpha_dummy_143) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_143, fv_syn_c1c] using (nb067_compact_fv_empty_0098)

theorem nb067_compact_fv_empty_0099 (f : Var) : (nb067_alpha_dummy_146 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0337 (f : Var) : (nb067_alpha_dummy_146 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_146, fv_syn_c1c] using (nb067_compact_fv_empty_0099 f)

theorem nb067_compact_fv_empty_0100 : (nb067_alpha_dummy_142) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0338 : (nb067_alpha_dummy_142) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_142, fv_syn_c1c] using (nb067_compact_fv_empty_0100)

theorem nb067_compact_fv_empty_0101 (f : Var) : (nb067_alpha_dummy_145 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0339 (f : Var) : (nb067_alpha_dummy_145 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_145, fv_syn_c1c] using (nb067_compact_fv_empty_0101 f)

theorem nb067_compact_fv_empty_0102 : (nb067_alpha_dummy_141) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0340 : (nb067_alpha_dummy_141) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_141, fv_syn_c1c] using (nb067_compact_fv_empty_0102)

theorem nb067_compact_fv_empty_0103 (f : Var) : (nb067_alpha_dummy_144 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0341 (f : Var) : (nb067_alpha_dummy_144 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_144, fv_syn_c1c] using (nb067_compact_fv_empty_0103 f)

theorem nb067_compact_fv_empty_0104 : (nb067_alpha_dummy_139) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0342 : (nb067_alpha_dummy_139) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_139, fv_syn_c1c] using (nb067_compact_fv_empty_0104)

theorem nb067_compact_fv_empty_0105 (f : Var) : (nb067_alpha_dummy_140 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0343 (f : Var) : (nb067_alpha_dummy_140 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_140, fv_syn_c1c] using (nb067_compact_fv_empty_0105 f)

theorem nb067_compact_fv_empty_0106 : (nb067_alpha_dummy_135) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0344 : (nb067_alpha_dummy_135) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_135, fv_syn_c1c] using (nb067_compact_fv_empty_0106)

theorem nb067_compact_fv_empty_0107 (f : Var) : (nb067_alpha_dummy_137 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0345 (f : Var) : (nb067_alpha_dummy_137 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_137, fv_syn_c1c] using (nb067_compact_fv_empty_0107 f)

theorem nb067_compact_fv_empty_0108 : (nb067_alpha_dummy_136) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0346 : (nb067_alpha_dummy_136) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_136, fv_syn_c1c] using (nb067_compact_fv_empty_0108)

theorem nb067_compact_fv_empty_0109 (f : Var) : (nb067_alpha_dummy_138 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0347 (f : Var) : (nb067_alpha_dummy_138 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_138, fv_syn_c1c] using (nb067_compact_fv_empty_0109 f)

theorem nb067_compact_fv_empty_0110 : (nb067_alpha_dummy_128) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0348 : (nb067_alpha_dummy_128) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_128, fv_syn_c1c] using (nb067_compact_fv_empty_0110)

theorem nb067_compact_fv_empty_0111 (f : Var) : (nb067_alpha_dummy_130 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0349 (f : Var) : (nb067_alpha_dummy_130 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_130, fv_syn_c1c] using (nb067_compact_fv_empty_0111 f)

theorem nb067_compact_fv_empty_0112 : (nb067_alpha_dummy_127) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0350 : (nb067_alpha_dummy_127) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_127, fv_syn_c1c] using (nb067_compact_fv_empty_0112)

theorem nb067_compact_fv_empty_0113 (f : Var) : (nb067_alpha_dummy_129 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0351 (f : Var) : (nb067_alpha_dummy_129 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_129, fv_syn_c1c] using (nb067_compact_fv_empty_0113 f)

theorem nb067_compact_fv_empty_0114 : (nb067_alpha_dummy_133) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0352 : (nb067_alpha_dummy_133) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_133, fv_syn_c1c] using (nb067_compact_fv_empty_0114)

theorem nb067_compact_fv_empty_0115 (f : Var) : (nb067_alpha_dummy_134 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0353 (f : Var) : (nb067_alpha_dummy_134 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_134, fv_syn_c1c] using (nb067_compact_fv_empty_0115 f)

theorem nb067_compact_fv_empty_0116 : (nb067_alpha_dummy_131) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0354 : (nb067_alpha_dummy_131) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_131, fv_syn_c1c] using (nb067_compact_fv_empty_0116)

theorem nb067_compact_fv_empty_0117 (f : Var) : (nb067_alpha_dummy_132 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0355 (f : Var) : (nb067_alpha_dummy_132 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_132, fv_syn_c1c] using (nb067_compact_fv_empty_0117 f)

theorem nb067_compact_fv_empty_0118 : (nb067_alpha_dummy_085) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0356 : (nb067_alpha_dummy_085) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_085, fv_syn_c1c] using (nb067_compact_fv_empty_0118)

theorem nb067_compact_fv_empty_0119 (f : Var) : (nb067_alpha_dummy_088 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0357 (f : Var) : (nb067_alpha_dummy_088 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_088, fv_syn_c1c] using (nb067_compact_fv_empty_0119 f)

theorem nb067_compact_envfresh_0022 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_143), (nb067_alpha_dummy_146 f)), ((nb067_alpha_dummy_142), (nb067_alpha_dummy_145 f)), ((nb067_alpha_dummy_141), (nb067_alpha_dummy_144 f)), ((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)), ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)), ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)), ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)), ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)), ((nb067_alpha_dummy_133), (nb067_alpha_dummy_134 f)), ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_143) (nb067_alpha_dummy_146 f) (nb067_wpp_notmem_0336) (nb067_wpp_notmem_0337 f) (TEnvFresh.consFresh (nb067_alpha_dummy_142) (nb067_alpha_dummy_145 f) (nb067_wpp_notmem_0338) (nb067_wpp_notmem_0339 f) (TEnvFresh.consFresh (nb067_alpha_dummy_141) (nb067_alpha_dummy_144 f) (nb067_wpp_notmem_0340) (nb067_wpp_notmem_0341 f) (TEnvFresh.consFresh (nb067_alpha_dummy_139) (nb067_alpha_dummy_140 f) (nb067_wpp_notmem_0342) (nb067_wpp_notmem_0343 f) (TEnvFresh.consFresh (nb067_alpha_dummy_135) (nb067_alpha_dummy_137 f) (nb067_wpp_notmem_0344) (nb067_wpp_notmem_0345 f) (TEnvFresh.consFresh (nb067_alpha_dummy_136) (nb067_alpha_dummy_138 f) (nb067_wpp_notmem_0346) (nb067_wpp_notmem_0347 f) (TEnvFresh.consFresh (nb067_alpha_dummy_128) (nb067_alpha_dummy_130 f) (nb067_wpp_notmem_0348) (nb067_wpp_notmem_0349 f) (TEnvFresh.consFresh (nb067_alpha_dummy_127) (nb067_alpha_dummy_129 f) (nb067_wpp_notmem_0350) (nb067_wpp_notmem_0351 f) (TEnvFresh.consFresh (nb067_alpha_dummy_133) (nb067_alpha_dummy_134 f) (nb067_wpp_notmem_0352) (nb067_wpp_notmem_0353 f) (TEnvFresh.consFresh (nb067_alpha_dummy_131) (nb067_alpha_dummy_132 f) (nb067_wpp_notmem_0354) (nb067_wpp_notmem_0355 f) (TEnvFresh.consFresh (nb067_alpha_dummy_085) (nb067_alpha_dummy_088 f) (nb067_wpp_notmem_0356) (nb067_wpp_notmem_0357 f) (TEnvFresh.consFresh (nb067_alpha_dummy_084) (nb067_alpha_dummy_087 f) (nb067_wpp_notmem_0226) (nb067_wpp_notmem_0227 f) (TEnvFresh.consFresh (nb067_alpha_dummy_083) (nb067_alpha_dummy_086 f) (nb067_wpp_notmem_0228) (nb067_wpp_notmem_0229 f) (TEnvFresh.consFresh (nb067_alpha_dummy_089) (nb067_alpha_dummy_090 f) (nb067_wpp_notmem_0230) (nb067_wpp_notmem_0231 f) (TEnvFresh.consFresh (nb067_alpha_dummy_081) (nb067_alpha_dummy_082 f) (nb067_wpp_notmem_0232) (nb067_wpp_notmem_0233 f) (TEnvFresh.consFresh (nb067_alpha_dummy_079) (nb067_alpha_dummy_080 f) (nb067_wpp_notmem_0234) (nb067_wpp_notmem_0235 f) (TEnvFresh.consFresh (nb067_alpha_dummy_000) f (nb067_wpp_notmem_0236) (nb067_wpp_notmem_0237 f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0028) (nb067_wpp_notmem_0029 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0030) (nb067_wpp_notmem_0031 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0032) (nb067_wpp_notmem_0033 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0034) (nb067_wpp_notmem_0035 x y f) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))))

noncomputable def nb067_wpp_refl_0022 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_143), (nb067_alpha_dummy_146 f)), ((nb067_alpha_dummy_142), (nb067_alpha_dummy_145 f)), ((nb067_alpha_dummy_141), (nb067_alpha_dummy_144 f)), ((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)), ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)), ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)), ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)), ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)), ((nb067_alpha_dummy_133), (nb067_alpha_dummy_134 f)), ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0022 x y f)

theorem nb067_wpp_notmem_0358 : (nb067_alpha_dummy_143) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_143, fv_syn_c0] using (nb067_compact_fv_empty_0098)

theorem nb067_wpp_notmem_0359 (f : Var) : (nb067_alpha_dummy_146 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_146, fv_syn_c0] using (nb067_compact_fv_empty_0099 f)

theorem nb067_wpp_notmem_0360 : (nb067_alpha_dummy_142) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_142, fv_syn_c0] using (nb067_compact_fv_empty_0100)

theorem nb067_wpp_notmem_0361 (f : Var) : (nb067_alpha_dummy_145 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_145, fv_syn_c0] using (nb067_compact_fv_empty_0101 f)

theorem nb067_wpp_notmem_0362 : (nb067_alpha_dummy_141) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_141, fv_syn_c0] using (nb067_compact_fv_empty_0102)

theorem nb067_wpp_notmem_0363 (f : Var) : (nb067_alpha_dummy_144 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_144, fv_syn_c0] using (nb067_compact_fv_empty_0103 f)

theorem nb067_wpp_notmem_0364 : (nb067_alpha_dummy_139) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_139, fv_syn_c0] using (nb067_compact_fv_empty_0104)

theorem nb067_wpp_notmem_0365 (f : Var) : (nb067_alpha_dummy_140 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_140, fv_syn_c0] using (nb067_compact_fv_empty_0105 f)

theorem nb067_wpp_notmem_0366 : (nb067_alpha_dummy_135) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_135, fv_syn_c0] using (nb067_compact_fv_empty_0106)

theorem nb067_wpp_notmem_0367 (f : Var) : (nb067_alpha_dummy_137 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_137, fv_syn_c0] using (nb067_compact_fv_empty_0107 f)

theorem nb067_wpp_notmem_0368 : (nb067_alpha_dummy_136) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_136, fv_syn_c0] using (nb067_compact_fv_empty_0108)

theorem nb067_wpp_notmem_0369 (f : Var) : (nb067_alpha_dummy_138 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_138, fv_syn_c0] using (nb067_compact_fv_empty_0109 f)

theorem nb067_wpp_notmem_0370 : (nb067_alpha_dummy_128) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_128, fv_syn_c0] using (nb067_compact_fv_empty_0110)

theorem nb067_wpp_notmem_0371 (f : Var) : (nb067_alpha_dummy_130 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_130, fv_syn_c0] using (nb067_compact_fv_empty_0111 f)

theorem nb067_wpp_notmem_0372 : (nb067_alpha_dummy_127) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_127, fv_syn_c0] using (nb067_compact_fv_empty_0112)

theorem nb067_wpp_notmem_0373 (f : Var) : (nb067_alpha_dummy_129 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_129, fv_syn_c0] using (nb067_compact_fv_empty_0113 f)

theorem nb067_wpp_notmem_0374 : (nb067_alpha_dummy_133) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_133, fv_syn_c0] using (nb067_compact_fv_empty_0114)

theorem nb067_wpp_notmem_0375 (f : Var) : (nb067_alpha_dummy_134 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_134, fv_syn_c0] using (nb067_compact_fv_empty_0115 f)

theorem nb067_wpp_notmem_0376 : (nb067_alpha_dummy_131) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_131, fv_syn_c0] using (nb067_compact_fv_empty_0116)

theorem nb067_wpp_notmem_0377 (f : Var) : (nb067_alpha_dummy_132 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_132, fv_syn_c0] using (nb067_compact_fv_empty_0117 f)

theorem nb067_wpp_notmem_0378 : (nb067_alpha_dummy_085) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_085, fv_syn_c0] using (nb067_compact_fv_empty_0118)

theorem nb067_wpp_notmem_0379 (f : Var) : (nb067_alpha_dummy_088 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_088, fv_syn_c0] using (nb067_compact_fv_empty_0119 f)

theorem nb067_compact_envfresh_0023 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_143), (nb067_alpha_dummy_146 f)), ((nb067_alpha_dummy_142), (nb067_alpha_dummy_145 f)), ((nb067_alpha_dummy_141), (nb067_alpha_dummy_144 f)), ((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)), ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)), ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)), ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)), ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)), ((nb067_alpha_dummy_133), (nb067_alpha_dummy_134 f)), ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_143) (nb067_alpha_dummy_146 f) (nb067_wpp_notmem_0358) (nb067_wpp_notmem_0359 f) (TEnvFresh.consFresh (nb067_alpha_dummy_142) (nb067_alpha_dummy_145 f) (nb067_wpp_notmem_0360) (nb067_wpp_notmem_0361 f) (TEnvFresh.consFresh (nb067_alpha_dummy_141) (nb067_alpha_dummy_144 f) (nb067_wpp_notmem_0362) (nb067_wpp_notmem_0363 f) (TEnvFresh.consFresh (nb067_alpha_dummy_139) (nb067_alpha_dummy_140 f) (nb067_wpp_notmem_0364) (nb067_wpp_notmem_0365 f) (TEnvFresh.consFresh (nb067_alpha_dummy_135) (nb067_alpha_dummy_137 f) (nb067_wpp_notmem_0366) (nb067_wpp_notmem_0367 f) (TEnvFresh.consFresh (nb067_alpha_dummy_136) (nb067_alpha_dummy_138 f) (nb067_wpp_notmem_0368) (nb067_wpp_notmem_0369 f) (TEnvFresh.consFresh (nb067_alpha_dummy_128) (nb067_alpha_dummy_130 f) (nb067_wpp_notmem_0370) (nb067_wpp_notmem_0371 f) (TEnvFresh.consFresh (nb067_alpha_dummy_127) (nb067_alpha_dummy_129 f) (nb067_wpp_notmem_0372) (nb067_wpp_notmem_0373 f) (TEnvFresh.consFresh (nb067_alpha_dummy_133) (nb067_alpha_dummy_134 f) (nb067_wpp_notmem_0374) (nb067_wpp_notmem_0375 f) (TEnvFresh.consFresh (nb067_alpha_dummy_131) (nb067_alpha_dummy_132 f) (nb067_wpp_notmem_0376) (nb067_wpp_notmem_0377 f) (TEnvFresh.consFresh (nb067_alpha_dummy_085) (nb067_alpha_dummy_088 f) (nb067_wpp_notmem_0378) (nb067_wpp_notmem_0379 f) (TEnvFresh.consFresh (nb067_alpha_dummy_084) (nb067_alpha_dummy_087 f) (nb067_wpp_notmem_0258) (nb067_wpp_notmem_0259 f) (TEnvFresh.consFresh (nb067_alpha_dummy_083) (nb067_alpha_dummy_086 f) (nb067_wpp_notmem_0260) (nb067_wpp_notmem_0261 f) (TEnvFresh.consFresh (nb067_alpha_dummy_089) (nb067_alpha_dummy_090 f) (nb067_wpp_notmem_0262) (nb067_wpp_notmem_0263 f) (TEnvFresh.consFresh (nb067_alpha_dummy_081) (nb067_alpha_dummy_082 f) (nb067_wpp_notmem_0264) (nb067_wpp_notmem_0265 f) (TEnvFresh.consFresh (nb067_alpha_dummy_079) (nb067_alpha_dummy_080 f) (nb067_wpp_notmem_0266) (nb067_wpp_notmem_0267 f) (TEnvFresh.consFresh (nb067_alpha_dummy_000) f (nb067_wpp_notmem_0268) (nb067_wpp_notmem_0269 f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0064) (nb067_wpp_notmem_0065 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0066) (nb067_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0068) (nb067_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0070) (nb067_wpp_notmem_0071 x y f) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))))

noncomputable def nb067_wpp_refl_0023 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_143), (nb067_alpha_dummy_146 f)), ((nb067_alpha_dummy_142), (nb067_alpha_dummy_145 f)), ((nb067_alpha_dummy_141), (nb067_alpha_dummy_144 f)), ((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)), ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)), ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)), ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)), ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)), ((nb067_alpha_dummy_133), (nb067_alpha_dummy_134 f)), ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0023 x y f)

noncomputable def nb067_split_alpha_0015 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb067_alpha_dummy_143), (nb067_alpha_dummy_146 f)), ((nb067_alpha_dummy_142), (nb067_alpha_dummy_145 f)), ((nb067_alpha_dummy_141), (nb067_alpha_dummy_144 f)), ((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)), ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)), ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)), ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)), ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)), ((nb067_alpha_dummy_133), (nb067_alpha_dummy_134 f)), ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_141)) (syn_cun (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_145 f)) (Class.cv (nb067_alpha_dummy_146 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_144 f)) (syn_cun (Class.cv (nb067_alpha_dummy_145 f)) (Class.cv (nb067_alpha_dummy_146 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0148) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0149 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0147 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0152) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0153 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0150) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0151 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0148) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0149 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0147 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0152) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0153 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0150) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0151 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_143), (nb067_alpha_dummy_146 f)), ((nb067_alpha_dummy_142), (nb067_alpha_dummy_145 f)), ((nb067_alpha_dummy_141), (nb067_alpha_dummy_144 f)), ((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)), ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)), ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)), ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)), ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)), ((nb067_alpha_dummy_133), (nb067_alpha_dummy_134 f)), ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_c0) (nb067_wpp_refl_0023 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0156) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0157 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0154) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0155 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0156) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0157 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0154) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0155 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0160) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0161 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0158) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0159 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0160) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0161 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0158) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0159 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb067_wpp_notmem_0380 : (nb067_alpha_dummy_139) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_139, fv_syn_cnnc] using (nb067_compact_fv_empty_0104)

theorem nb067_wpp_notmem_0381 (f : Var) : (nb067_alpha_dummy_140 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_140, fv_syn_cnnc] using (nb067_compact_fv_empty_0105 f)

theorem nb067_wpp_notmem_0382 : (nb067_alpha_dummy_135) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_135, fv_syn_cnnc] using (nb067_compact_fv_empty_0106)

theorem nb067_wpp_notmem_0383 (f : Var) : (nb067_alpha_dummy_137 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_137, fv_syn_cnnc] using (nb067_compact_fv_empty_0107 f)

theorem nb067_wpp_notmem_0384 : (nb067_alpha_dummy_136) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_136, fv_syn_cnnc] using (nb067_compact_fv_empty_0108)

theorem nb067_wpp_notmem_0385 (f : Var) : (nb067_alpha_dummy_138 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_138, fv_syn_cnnc] using (nb067_compact_fv_empty_0109 f)

theorem nb067_wpp_notmem_0386 : (nb067_alpha_dummy_128) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_128, fv_syn_cnnc] using (nb067_compact_fv_empty_0110)

theorem nb067_wpp_notmem_0387 (f : Var) : (nb067_alpha_dummy_130 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_130, fv_syn_cnnc] using (nb067_compact_fv_empty_0111 f)

theorem nb067_wpp_notmem_0388 : (nb067_alpha_dummy_127) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_127, fv_syn_cnnc] using (nb067_compact_fv_empty_0112)

theorem nb067_wpp_notmem_0389 (f : Var) : (nb067_alpha_dummy_129 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_129, fv_syn_cnnc] using (nb067_compact_fv_empty_0113 f)

theorem nb067_wpp_notmem_0390 : (nb067_alpha_dummy_133) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_133, fv_syn_cnnc] using (nb067_compact_fv_empty_0114)

theorem nb067_wpp_notmem_0391 (f : Var) : (nb067_alpha_dummy_134 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_134, fv_syn_cnnc] using (nb067_compact_fv_empty_0115 f)

theorem nb067_wpp_notmem_0392 : (nb067_alpha_dummy_131) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_131, fv_syn_cnnc] using (nb067_compact_fv_empty_0116)

theorem nb067_wpp_notmem_0393 (f : Var) : (nb067_alpha_dummy_132 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_132, fv_syn_cnnc] using (nb067_compact_fv_empty_0117 f)

theorem nb067_wpp_notmem_0394 : (nb067_alpha_dummy_085) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_085, fv_syn_cnnc] using (nb067_compact_fv_empty_0118)

theorem nb067_wpp_notmem_0395 (f : Var) : (nb067_alpha_dummy_088 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_088, fv_syn_cnnc] using (nb067_compact_fv_empty_0119 f)

theorem nb067_compact_envfresh_0024 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)), ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)), ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)), ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)), ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)), ((nb067_alpha_dummy_133), (nb067_alpha_dummy_134 f)), ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_139) (nb067_alpha_dummy_140 f) (nb067_wpp_notmem_0380) (nb067_wpp_notmem_0381 f) (TEnvFresh.consFresh (nb067_alpha_dummy_135) (nb067_alpha_dummy_137 f) (nb067_wpp_notmem_0382) (nb067_wpp_notmem_0383 f) (TEnvFresh.consFresh (nb067_alpha_dummy_136) (nb067_alpha_dummy_138 f) (nb067_wpp_notmem_0384) (nb067_wpp_notmem_0385 f) (TEnvFresh.consFresh (nb067_alpha_dummy_128) (nb067_alpha_dummy_130 f) (nb067_wpp_notmem_0386) (nb067_wpp_notmem_0387 f) (TEnvFresh.consFresh (nb067_alpha_dummy_127) (nb067_alpha_dummy_129 f) (nb067_wpp_notmem_0388) (nb067_wpp_notmem_0389 f) (TEnvFresh.consFresh (nb067_alpha_dummy_133) (nb067_alpha_dummy_134 f) (nb067_wpp_notmem_0390) (nb067_wpp_notmem_0391 f) (TEnvFresh.consFresh (nb067_alpha_dummy_131) (nb067_alpha_dummy_132 f) (nb067_wpp_notmem_0392) (nb067_wpp_notmem_0393 f) (TEnvFresh.consFresh (nb067_alpha_dummy_085) (nb067_alpha_dummy_088 f) (nb067_wpp_notmem_0394) (nb067_wpp_notmem_0395 f) (TEnvFresh.consFresh (nb067_alpha_dummy_084) (nb067_alpha_dummy_087 f) (nb067_wpp_notmem_0284) (nb067_wpp_notmem_0285 f) (TEnvFresh.consFresh (nb067_alpha_dummy_083) (nb067_alpha_dummy_086 f) (nb067_wpp_notmem_0286) (nb067_wpp_notmem_0287 f) (TEnvFresh.consFresh (nb067_alpha_dummy_089) (nb067_alpha_dummy_090 f) (nb067_wpp_notmem_0288) (nb067_wpp_notmem_0289 f) (TEnvFresh.consFresh (nb067_alpha_dummy_081) (nb067_alpha_dummy_082 f) (nb067_wpp_notmem_0290) (nb067_wpp_notmem_0291 f) (TEnvFresh.consFresh (nb067_alpha_dummy_079) (nb067_alpha_dummy_080 f) (nb067_wpp_notmem_0292) (nb067_wpp_notmem_0293 f) (TEnvFresh.consFresh (nb067_alpha_dummy_000) f (nb067_wpp_notmem_0294) (nb067_wpp_notmem_0295 f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0094) (nb067_wpp_notmem_0095 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0096) (nb067_wpp_notmem_0097 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0098) (nb067_wpp_notmem_0099 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0100) (nb067_wpp_notmem_0101 x y f) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))))

noncomputable def nb067_wpp_refl_0024 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)), ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)), ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)), ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)), ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)), ((nb067_alpha_dummy_133), (nb067_alpha_dummy_134 f)), ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0024 x y f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
