import NAR4C056C001Part009

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

noncomputable def nb056_split_alpha_0013 (f : Var) : TAlphaWff [((nb056_alpha_dummy_099), (nb056_alpha_dummy_101 f)), ((nb056_alpha_dummy_100), (nb056_alpha_dummy_102 f)), ((nb056_alpha_dummy_125), (nb056_alpha_dummy_126 f)), ((nb056_alpha_dummy_123), (nb056_alpha_dummy_124 f)), ((nb056_alpha_dummy_092), (nb056_alpha_dummy_094 f)), ((nb056_alpha_dummy_091), (nb056_alpha_dummy_093 f)), ((nb056_alpha_dummy_121), (nb056_alpha_dummy_122 f)), ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)), ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)), ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)), ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (Wff.classEq (Class.cv (nb056_alpha_dummy_100)) (syn_cif (Wff.classMem (Class.cv (nb056_alpha_dummy_099)) (syn_cnnc)) (syn_cplc (Class.cv (nb056_alpha_dummy_099)) (syn_c1c)) (Class.cv (nb056_alpha_dummy_099)))) (Wff.classEq (Class.cv (nb056_alpha_dummy_102 f)) (syn_cif (Wff.classMem (Class.cv (nb056_alpha_dummy_101 f)) (syn_cnnc)) (syn_cplc (Class.cv (nb056_alpha_dummy_101 f)) (syn_c1c)) (Class.cv (nb056_alpha_dummy_101 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_092))).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_094 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0094) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0095 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0094) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0095 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0093 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_107), (nb056_alpha_dummy_110 f)), ((nb056_alpha_dummy_106), (nb056_alpha_dummy_109 f)), ((nb056_alpha_dummy_105), (nb056_alpha_dummy_108 f)), ((nb056_alpha_dummy_103), (nb056_alpha_dummy_104 f)), ((nb056_alpha_dummy_099), (nb056_alpha_dummy_101 f)), ((nb056_alpha_dummy_100), (nb056_alpha_dummy_102 f)), ((nb056_alpha_dummy_125), (nb056_alpha_dummy_126 f)), ((nb056_alpha_dummy_123), (nb056_alpha_dummy_124 f)), ((nb056_alpha_dummy_092), (nb056_alpha_dummy_094 f)), ((nb056_alpha_dummy_091), (nb056_alpha_dummy_093 f)), ((nb056_alpha_dummy_121), (nb056_alpha_dummy_122 f)), ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)), ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)), ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)), ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_c1c) (nb056_wpp_refl_0017 f))) (TAlphaWff.neg (TAlphaWff.neg (nb056_split_alpha_0012 f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0093 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_103), (nb056_alpha_dummy_104 f)), ((nb056_alpha_dummy_099), (nb056_alpha_dummy_101 f)), ((nb056_alpha_dummy_100), (nb056_alpha_dummy_102 f)), ((nb056_alpha_dummy_125), (nb056_alpha_dummy_126 f)), ((nb056_alpha_dummy_123), (nb056_alpha_dummy_124 f)), ((nb056_alpha_dummy_092), (nb056_alpha_dummy_094 f)), ((nb056_alpha_dummy_091), (nb056_alpha_dummy_093 f)), ((nb056_alpha_dummy_121), (nb056_alpha_dummy_122 f)), ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)), ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)), ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)), ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_cnnc) (nb056_wpp_refl_0019 f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0093 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0093 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_103), (nb056_alpha_dummy_104 f)), ((nb056_alpha_dummy_099), (nb056_alpha_dummy_101 f)), ((nb056_alpha_dummy_100), (nb056_alpha_dummy_102 f)), ((nb056_alpha_dummy_125), (nb056_alpha_dummy_126 f)), ((nb056_alpha_dummy_123), (nb056_alpha_dummy_124 f)), ((nb056_alpha_dummy_092), (nb056_alpha_dummy_094 f)), ((nb056_alpha_dummy_091), (nb056_alpha_dummy_093 f)), ((nb056_alpha_dummy_121), (nb056_alpha_dummy_122 f)), ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)), ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)), ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)), ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_cnnc) (nb056_wpp_refl_0019 f))))))))))

theorem nb056_wpp_notmem_0310 : (nb056_alpha_dummy_123) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_123, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0094)

theorem nb056_wpp_notmem_0311 (f : Var) : (nb056_alpha_dummy_124 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_124, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0095 f)

theorem nb056_wpp_notmem_0312 : (nb056_alpha_dummy_092) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_092, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0078)

theorem nb056_wpp_notmem_0313 (f : Var) : (nb056_alpha_dummy_094 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_094, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0079 f)

theorem nb056_wpp_notmem_0314 : (nb056_alpha_dummy_091) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_091, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0080)

theorem nb056_wpp_notmem_0315 (f : Var) : (nb056_alpha_dummy_093 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_093, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0081 f)

theorem nb056_wpp_notmem_0316 : (nb056_alpha_dummy_121) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_121, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0096)

theorem nb056_wpp_notmem_0317 (f : Var) : (nb056_alpha_dummy_122 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_122, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0097 f)

theorem nb056_wpp_notmem_0318 : (nb056_alpha_dummy_095) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_095, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0084)

theorem nb056_wpp_notmem_0319 (f : Var) : (nb056_alpha_dummy_096 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_096, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0085 f)

theorem nb056_wpp_notmem_0320 : (nb056_alpha_dummy_086) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_086, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0086)

theorem nb056_wpp_notmem_0321 (f : Var) : (nb056_alpha_dummy_088 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_088, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0087 f)

theorem nb056_wpp_notmem_0322 : (nb056_alpha_dummy_085) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_085, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0088)

theorem nb056_wpp_notmem_0323 (f : Var) : (nb056_alpha_dummy_087 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_087, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0089 f)

theorem nb056_wpp_notmem_0324 : (nb056_alpha_dummy_089) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_089, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0090)

theorem nb056_wpp_notmem_0325 (f : Var) : (nb056_alpha_dummy_090 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_090, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0091 f)

theorem nb056_compact_envfresh_0020 (f : Var) : TEnvFresh [((nb056_alpha_dummy_123), (nb056_alpha_dummy_124 f)), ((nb056_alpha_dummy_092), (nb056_alpha_dummy_094 f)), ((nb056_alpha_dummy_091), (nb056_alpha_dummy_093 f)), ((nb056_alpha_dummy_121), (nb056_alpha_dummy_122 f)), ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)), ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)), ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)), ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb056_alpha_dummy_123) (nb056_alpha_dummy_124 f) (nb056_wpp_notmem_0310) (nb056_wpp_notmem_0311 f) (TEnvFresh.consFresh (nb056_alpha_dummy_092) (nb056_alpha_dummy_094 f) (nb056_wpp_notmem_0312) (nb056_wpp_notmem_0313 f) (TEnvFresh.consFresh (nb056_alpha_dummy_091) (nb056_alpha_dummy_093 f) (nb056_wpp_notmem_0314) (nb056_wpp_notmem_0315 f) (TEnvFresh.consFresh (nb056_alpha_dummy_121) (nb056_alpha_dummy_122 f) (nb056_wpp_notmem_0316) (nb056_wpp_notmem_0317 f) (TEnvFresh.consFresh (nb056_alpha_dummy_095) (nb056_alpha_dummy_096 f) (nb056_wpp_notmem_0318) (nb056_wpp_notmem_0319 f) (TEnvFresh.consFresh (nb056_alpha_dummy_086) (nb056_alpha_dummy_088 f) (nb056_wpp_notmem_0320) (nb056_wpp_notmem_0321 f) (TEnvFresh.consFresh (nb056_alpha_dummy_085) (nb056_alpha_dummy_087 f) (nb056_wpp_notmem_0322) (nb056_wpp_notmem_0323 f) (TEnvFresh.consFresh (nb056_alpha_dummy_089) (nb056_alpha_dummy_090 f) (nb056_wpp_notmem_0324) (nb056_wpp_notmem_0325 f) (TEnvFresh.consFresh (nb056_alpha_dummy_007) (nb056_alpha_dummy_010 f) (nb056_wpp_notmem_0218) (nb056_wpp_notmem_0219 f) (TEnvFresh.consFresh (nb056_alpha_dummy_006) (nb056_alpha_dummy_009 f) (nb056_wpp_notmem_0118) (nb056_wpp_notmem_0119 f) (TEnvFresh.consFresh (nb056_alpha_dummy_005) (nb056_alpha_dummy_008 f) (nb056_wpp_notmem_0120) (nb056_wpp_notmem_0121 f) (TEnvFresh.consFresh (nb056_alpha_dummy_011) (nb056_alpha_dummy_012 f) (nb056_wpp_notmem_0122) (nb056_wpp_notmem_0123 f) (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f) (nb056_wpp_notmem_0124) (nb056_wpp_notmem_0125 f) (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f) (nb056_wpp_notmem_0126) (nb056_wpp_notmem_0127 f) (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0128) (nb056_wpp_notmem_0129 f) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))))

noncomputable def nb056_wpp_refl_0020 (f : Var) : TReflOn [((nb056_alpha_dummy_123), (nb056_alpha_dummy_124 f)), ((nb056_alpha_dummy_092), (nb056_alpha_dummy_094 f)), ((nb056_alpha_dummy_091), (nb056_alpha_dummy_093 f)), ((nb056_alpha_dummy_121), (nb056_alpha_dummy_122 f)), ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)), ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)), ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)), ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0020 f)

noncomputable def nb056_split_alpha_0014 (f : Var) : TAlphaWff [((nb056_alpha_dummy_121), (nb056_alpha_dummy_122 f)), ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)), ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)), ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)), ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_121)) (Class.cab (nb056_alpha_dummy_091) (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086)) (Wff.classEq (Class.cv (nb056_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb056_alpha_dummy_121)) (Class.cab (nb056_alpha_dummy_091) (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086)) (Wff.classEq (Class.cv (nb056_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092))) (syn_csn (syn_c0c))))))))) (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_122 f)) (Class.cab (nb056_alpha_dummy_093 f) (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb056_alpha_dummy_122 f)) (Class.cab (nb056_alpha_dummy_093 f) (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))) (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0112) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0114 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0112) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0114 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0116) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0117 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0113) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0115 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_085))).fv ∪ ((Class.cv (nb056_alpha_dummy_086))).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_087 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_088 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0090) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0091 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0090) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0091 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0120) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0121 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0118) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0119 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (nb056_split_alpha_0013 f))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0090) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0091 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0090) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0091 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0120) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0121 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0118) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0119 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (nb056_split_alpha_0013 f))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_123), (nb056_alpha_dummy_124 f)), ((nb056_alpha_dummy_092), (nb056_alpha_dummy_094 f)), ((nb056_alpha_dummy_091), (nb056_alpha_dummy_093 f)), ((nb056_alpha_dummy_121), (nb056_alpha_dummy_122 f)), ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)), ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)), ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)), ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_ccompl (syn_csn (syn_c0c))) (nb056_wpp_refl_0020 f))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0112) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0114 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0112) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0114 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0116) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0117 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0113) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0115 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_085))).fv ∪ ((Class.cv (nb056_alpha_dummy_086))).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_087 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_088 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0090) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0091 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0090) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0091 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0120) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0121 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0118) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0119 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (nb056_split_alpha_0013 f))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0090) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0091 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0090) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0091 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0120) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0121 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0118) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0119 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (nb056_split_alpha_0013 f))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_123), (nb056_alpha_dummy_124 f)), ((nb056_alpha_dummy_092), (nb056_alpha_dummy_094 f)), ((nb056_alpha_dummy_091), (nb056_alpha_dummy_093 f)), ((nb056_alpha_dummy_121), (nb056_alpha_dummy_122 f)), ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)), ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)), ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)), ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_ccompl (syn_csn (syn_c0c))) (nb056_wpp_refl_0020 f)))))))))))))))))))

theorem nb056_compact_fv_empty_0098 : (nb056_alpha_dummy_143) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0326 : (nb056_alpha_dummy_143) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_143, fv_syn_c1c] using (nb056_compact_fv_empty_0098)

theorem nb056_compact_fv_empty_0099 (f : Var) : (nb056_alpha_dummy_146 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0327 (f : Var) : (nb056_alpha_dummy_146 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_146, fv_syn_c1c] using (nb056_compact_fv_empty_0099 f)

theorem nb056_compact_fv_empty_0100 : (nb056_alpha_dummy_142) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0328 : (nb056_alpha_dummy_142) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_142, fv_syn_c1c] using (nb056_compact_fv_empty_0100)

theorem nb056_compact_fv_empty_0101 (f : Var) : (nb056_alpha_dummy_145 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0329 (f : Var) : (nb056_alpha_dummy_145 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_145, fv_syn_c1c] using (nb056_compact_fv_empty_0101 f)

theorem nb056_compact_fv_empty_0102 : (nb056_alpha_dummy_141) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0330 : (nb056_alpha_dummy_141) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_141, fv_syn_c1c] using (nb056_compact_fv_empty_0102)

theorem nb056_compact_fv_empty_0103 (f : Var) : (nb056_alpha_dummy_144 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0331 (f : Var) : (nb056_alpha_dummy_144 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_144, fv_syn_c1c] using (nb056_compact_fv_empty_0103 f)

theorem nb056_compact_fv_empty_0104 : (nb056_alpha_dummy_139) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0332 : (nb056_alpha_dummy_139) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_139, fv_syn_c1c] using (nb056_compact_fv_empty_0104)

theorem nb056_compact_fv_empty_0105 (f : Var) : (nb056_alpha_dummy_140 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0333 (f : Var) : (nb056_alpha_dummy_140 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_140, fv_syn_c1c] using (nb056_compact_fv_empty_0105 f)

theorem nb056_compact_fv_empty_0106 : (nb056_alpha_dummy_135) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0334 : (nb056_alpha_dummy_135) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_135, fv_syn_c1c] using (nb056_compact_fv_empty_0106)

theorem nb056_compact_fv_empty_0107 (f : Var) : (nb056_alpha_dummy_137 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0335 (f : Var) : (nb056_alpha_dummy_137 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_137, fv_syn_c1c] using (nb056_compact_fv_empty_0107 f)

theorem nb056_compact_fv_empty_0108 : (nb056_alpha_dummy_136) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0336 : (nb056_alpha_dummy_136) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_136, fv_syn_c1c] using (nb056_compact_fv_empty_0108)

theorem nb056_compact_fv_empty_0109 (f : Var) : (nb056_alpha_dummy_138 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0337 (f : Var) : (nb056_alpha_dummy_138 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_138, fv_syn_c1c] using (nb056_compact_fv_empty_0109 f)

theorem nb056_compact_fv_empty_0110 : (nb056_alpha_dummy_128) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0338 : (nb056_alpha_dummy_128) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_128, fv_syn_c1c] using (nb056_compact_fv_empty_0110)

theorem nb056_compact_fv_empty_0111 (f : Var) : (nb056_alpha_dummy_130 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0339 (f : Var) : (nb056_alpha_dummy_130 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_130, fv_syn_c1c] using (nb056_compact_fv_empty_0111 f)

theorem nb056_compact_fv_empty_0112 : (nb056_alpha_dummy_127) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0340 : (nb056_alpha_dummy_127) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_127, fv_syn_c1c] using (nb056_compact_fv_empty_0112)

theorem nb056_compact_fv_empty_0113 (f : Var) : (nb056_alpha_dummy_129 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0341 (f : Var) : (nb056_alpha_dummy_129 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_129, fv_syn_c1c] using (nb056_compact_fv_empty_0113 f)

theorem nb056_compact_fv_empty_0114 : (nb056_alpha_dummy_133) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0342 : (nb056_alpha_dummy_133) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_133, fv_syn_c1c] using (nb056_compact_fv_empty_0114)

theorem nb056_compact_fv_empty_0115 (f : Var) : (nb056_alpha_dummy_134 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0343 (f : Var) : (nb056_alpha_dummy_134 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_134, fv_syn_c1c] using (nb056_compact_fv_empty_0115 f)

theorem nb056_compact_fv_empty_0116 : (nb056_alpha_dummy_131) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0344 : (nb056_alpha_dummy_131) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_131, fv_syn_c1c] using (nb056_compact_fv_empty_0116)

theorem nb056_compact_fv_empty_0117 (f : Var) : (nb056_alpha_dummy_132 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0345 (f : Var) : (nb056_alpha_dummy_132 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_132, fv_syn_c1c] using (nb056_compact_fv_empty_0117 f)

theorem nb056_compact_envfresh_0021 (f : Var) : TEnvFresh [((nb056_alpha_dummy_143), (nb056_alpha_dummy_146 f)), ((nb056_alpha_dummy_142), (nb056_alpha_dummy_145 f)), ((nb056_alpha_dummy_141), (nb056_alpha_dummy_144 f)), ((nb056_alpha_dummy_139), (nb056_alpha_dummy_140 f)), ((nb056_alpha_dummy_135), (nb056_alpha_dummy_137 f)), ((nb056_alpha_dummy_136), (nb056_alpha_dummy_138 f)), ((nb056_alpha_dummy_128), (nb056_alpha_dummy_130 f)), ((nb056_alpha_dummy_127), (nb056_alpha_dummy_129 f)), ((nb056_alpha_dummy_133), (nb056_alpha_dummy_134 f)), ((nb056_alpha_dummy_131), (nb056_alpha_dummy_132 f)), ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)), ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)), ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb056_alpha_dummy_143) (nb056_alpha_dummy_146 f) (nb056_wpp_notmem_0326) (nb056_wpp_notmem_0327 f) (TEnvFresh.consFresh (nb056_alpha_dummy_142) (nb056_alpha_dummy_145 f) (nb056_wpp_notmem_0328) (nb056_wpp_notmem_0329 f) (TEnvFresh.consFresh (nb056_alpha_dummy_141) (nb056_alpha_dummy_144 f) (nb056_wpp_notmem_0330) (nb056_wpp_notmem_0331 f) (TEnvFresh.consFresh (nb056_alpha_dummy_139) (nb056_alpha_dummy_140 f) (nb056_wpp_notmem_0332) (nb056_wpp_notmem_0333 f) (TEnvFresh.consFresh (nb056_alpha_dummy_135) (nb056_alpha_dummy_137 f) (nb056_wpp_notmem_0334) (nb056_wpp_notmem_0335 f) (TEnvFresh.consFresh (nb056_alpha_dummy_136) (nb056_alpha_dummy_138 f) (nb056_wpp_notmem_0336) (nb056_wpp_notmem_0337 f) (TEnvFresh.consFresh (nb056_alpha_dummy_128) (nb056_alpha_dummy_130 f) (nb056_wpp_notmem_0338) (nb056_wpp_notmem_0339 f) (TEnvFresh.consFresh (nb056_alpha_dummy_127) (nb056_alpha_dummy_129 f) (nb056_wpp_notmem_0340) (nb056_wpp_notmem_0341 f) (TEnvFresh.consFresh (nb056_alpha_dummy_133) (nb056_alpha_dummy_134 f) (nb056_wpp_notmem_0342) (nb056_wpp_notmem_0343 f) (TEnvFresh.consFresh (nb056_alpha_dummy_131) (nb056_alpha_dummy_132 f) (nb056_wpp_notmem_0344) (nb056_wpp_notmem_0345 f) (TEnvFresh.consFresh (nb056_alpha_dummy_086) (nb056_alpha_dummy_088 f) (nb056_wpp_notmem_0240) (nb056_wpp_notmem_0241 f) (TEnvFresh.consFresh (nb056_alpha_dummy_085) (nb056_alpha_dummy_087 f) (nb056_wpp_notmem_0242) (nb056_wpp_notmem_0243 f) (TEnvFresh.consFresh (nb056_alpha_dummy_089) (nb056_alpha_dummy_090 f) (nb056_wpp_notmem_0244) (nb056_wpp_notmem_0245 f) (TEnvFresh.consFresh (nb056_alpha_dummy_007) (nb056_alpha_dummy_010 f) (nb056_wpp_notmem_0150) (nb056_wpp_notmem_0151 f) (TEnvFresh.consFresh (nb056_alpha_dummy_006) (nb056_alpha_dummy_009 f) (nb056_wpp_notmem_0020) (nb056_wpp_notmem_0021 f) (TEnvFresh.consFresh (nb056_alpha_dummy_005) (nb056_alpha_dummy_008 f) (nb056_wpp_notmem_0022) (nb056_wpp_notmem_0023 f) (TEnvFresh.consFresh (nb056_alpha_dummy_011) (nb056_alpha_dummy_012 f) (nb056_wpp_notmem_0024) (nb056_wpp_notmem_0025 f) (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f) (nb056_wpp_notmem_0026) (nb056_wpp_notmem_0027 f) (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f) (nb056_wpp_notmem_0028) (nb056_wpp_notmem_0029 f) (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0030) (nb056_wpp_notmem_0031 f) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))

noncomputable def nb056_wpp_refl_0021 (f : Var) : TReflOn [((nb056_alpha_dummy_143), (nb056_alpha_dummy_146 f)), ((nb056_alpha_dummy_142), (nb056_alpha_dummy_145 f)), ((nb056_alpha_dummy_141), (nb056_alpha_dummy_144 f)), ((nb056_alpha_dummy_139), (nb056_alpha_dummy_140 f)), ((nb056_alpha_dummy_135), (nb056_alpha_dummy_137 f)), ((nb056_alpha_dummy_136), (nb056_alpha_dummy_138 f)), ((nb056_alpha_dummy_128), (nb056_alpha_dummy_130 f)), ((nb056_alpha_dummy_127), (nb056_alpha_dummy_129 f)), ((nb056_alpha_dummy_133), (nb056_alpha_dummy_134 f)), ((nb056_alpha_dummy_131), (nb056_alpha_dummy_132 f)), ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)), ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)), ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0021 f)

theorem nb056_wpp_notmem_0346 : (nb056_alpha_dummy_143) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_143, fv_syn_c0] using (nb056_compact_fv_empty_0098)

theorem nb056_wpp_notmem_0347 (f : Var) : (nb056_alpha_dummy_146 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_146, fv_syn_c0] using (nb056_compact_fv_empty_0099 f)

theorem nb056_wpp_notmem_0348 : (nb056_alpha_dummy_142) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_142, fv_syn_c0] using (nb056_compact_fv_empty_0100)

theorem nb056_wpp_notmem_0349 (f : Var) : (nb056_alpha_dummy_145 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_145, fv_syn_c0] using (nb056_compact_fv_empty_0101 f)

theorem nb056_wpp_notmem_0350 : (nb056_alpha_dummy_141) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_141, fv_syn_c0] using (nb056_compact_fv_empty_0102)

theorem nb056_wpp_notmem_0351 (f : Var) : (nb056_alpha_dummy_144 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_144, fv_syn_c0] using (nb056_compact_fv_empty_0103 f)

theorem nb056_wpp_notmem_0352 : (nb056_alpha_dummy_139) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_139, fv_syn_c0] using (nb056_compact_fv_empty_0104)

theorem nb056_wpp_notmem_0353 (f : Var) : (nb056_alpha_dummy_140 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_140, fv_syn_c0] using (nb056_compact_fv_empty_0105 f)

theorem nb056_wpp_notmem_0354 : (nb056_alpha_dummy_135) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_135, fv_syn_c0] using (nb056_compact_fv_empty_0106)

theorem nb056_wpp_notmem_0355 (f : Var) : (nb056_alpha_dummy_137 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_137, fv_syn_c0] using (nb056_compact_fv_empty_0107 f)

theorem nb056_wpp_notmem_0356 : (nb056_alpha_dummy_136) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_136, fv_syn_c0] using (nb056_compact_fv_empty_0108)

theorem nb056_wpp_notmem_0357 (f : Var) : (nb056_alpha_dummy_138 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_138, fv_syn_c0] using (nb056_compact_fv_empty_0109 f)

theorem nb056_wpp_notmem_0358 : (nb056_alpha_dummy_128) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_128, fv_syn_c0] using (nb056_compact_fv_empty_0110)

theorem nb056_wpp_notmem_0359 (f : Var) : (nb056_alpha_dummy_130 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_130, fv_syn_c0] using (nb056_compact_fv_empty_0111 f)

theorem nb056_wpp_notmem_0360 : (nb056_alpha_dummy_127) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_127, fv_syn_c0] using (nb056_compact_fv_empty_0112)

theorem nb056_wpp_notmem_0361 (f : Var) : (nb056_alpha_dummy_129 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_129, fv_syn_c0] using (nb056_compact_fv_empty_0113 f)

theorem nb056_wpp_notmem_0362 : (nb056_alpha_dummy_133) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_133, fv_syn_c0] using (nb056_compact_fv_empty_0114)

theorem nb056_wpp_notmem_0363 (f : Var) : (nb056_alpha_dummy_134 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_134, fv_syn_c0] using (nb056_compact_fv_empty_0115 f)

theorem nb056_wpp_notmem_0364 : (nb056_alpha_dummy_131) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_131, fv_syn_c0] using (nb056_compact_fv_empty_0116)

theorem nb056_wpp_notmem_0365 (f : Var) : (nb056_alpha_dummy_132 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_132, fv_syn_c0] using (nb056_compact_fv_empty_0117 f)

theorem nb056_compact_envfresh_0022 (f : Var) : TEnvFresh [((nb056_alpha_dummy_143), (nb056_alpha_dummy_146 f)), ((nb056_alpha_dummy_142), (nb056_alpha_dummy_145 f)), ((nb056_alpha_dummy_141), (nb056_alpha_dummy_144 f)), ((nb056_alpha_dummy_139), (nb056_alpha_dummy_140 f)), ((nb056_alpha_dummy_135), (nb056_alpha_dummy_137 f)), ((nb056_alpha_dummy_136), (nb056_alpha_dummy_138 f)), ((nb056_alpha_dummy_128), (nb056_alpha_dummy_130 f)), ((nb056_alpha_dummy_127), (nb056_alpha_dummy_129 f)), ((nb056_alpha_dummy_133), (nb056_alpha_dummy_134 f)), ((nb056_alpha_dummy_131), (nb056_alpha_dummy_132 f)), ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)), ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)), ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb056_alpha_dummy_143) (nb056_alpha_dummy_146 f) (nb056_wpp_notmem_0346) (nb056_wpp_notmem_0347 f) (TEnvFresh.consFresh (nb056_alpha_dummy_142) (nb056_alpha_dummy_145 f) (nb056_wpp_notmem_0348) (nb056_wpp_notmem_0349 f) (TEnvFresh.consFresh (nb056_alpha_dummy_141) (nb056_alpha_dummy_144 f) (nb056_wpp_notmem_0350) (nb056_wpp_notmem_0351 f) (TEnvFresh.consFresh (nb056_alpha_dummy_139) (nb056_alpha_dummy_140 f) (nb056_wpp_notmem_0352) (nb056_wpp_notmem_0353 f) (TEnvFresh.consFresh (nb056_alpha_dummy_135) (nb056_alpha_dummy_137 f) (nb056_wpp_notmem_0354) (nb056_wpp_notmem_0355 f) (TEnvFresh.consFresh (nb056_alpha_dummy_136) (nb056_alpha_dummy_138 f) (nb056_wpp_notmem_0356) (nb056_wpp_notmem_0357 f) (TEnvFresh.consFresh (nb056_alpha_dummy_128) (nb056_alpha_dummy_130 f) (nb056_wpp_notmem_0358) (nb056_wpp_notmem_0359 f) (TEnvFresh.consFresh (nb056_alpha_dummy_127) (nb056_alpha_dummy_129 f) (nb056_wpp_notmem_0360) (nb056_wpp_notmem_0361 f) (TEnvFresh.consFresh (nb056_alpha_dummy_133) (nb056_alpha_dummy_134 f) (nb056_wpp_notmem_0362) (nb056_wpp_notmem_0363 f) (TEnvFresh.consFresh (nb056_alpha_dummy_131) (nb056_alpha_dummy_132 f) (nb056_wpp_notmem_0364) (nb056_wpp_notmem_0365 f) (TEnvFresh.consFresh (nb056_alpha_dummy_086) (nb056_alpha_dummy_088 f) (nb056_wpp_notmem_0266) (nb056_wpp_notmem_0267 f) (TEnvFresh.consFresh (nb056_alpha_dummy_085) (nb056_alpha_dummy_087 f) (nb056_wpp_notmem_0268) (nb056_wpp_notmem_0269 f) (TEnvFresh.consFresh (nb056_alpha_dummy_089) (nb056_alpha_dummy_090 f) (nb056_wpp_notmem_0270) (nb056_wpp_notmem_0271 f) (TEnvFresh.consFresh (nb056_alpha_dummy_007) (nb056_alpha_dummy_010 f) (nb056_wpp_notmem_0172) (nb056_wpp_notmem_0173 f) (TEnvFresh.consFresh (nb056_alpha_dummy_006) (nb056_alpha_dummy_009 f) (nb056_wpp_notmem_0052) (nb056_wpp_notmem_0053 f) (TEnvFresh.consFresh (nb056_alpha_dummy_005) (nb056_alpha_dummy_008 f) (nb056_wpp_notmem_0054) (nb056_wpp_notmem_0055 f) (TEnvFresh.consFresh (nb056_alpha_dummy_011) (nb056_alpha_dummy_012 f) (nb056_wpp_notmem_0056) (nb056_wpp_notmem_0057 f) (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f) (nb056_wpp_notmem_0058) (nb056_wpp_notmem_0059 f) (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f) (nb056_wpp_notmem_0060) (nb056_wpp_notmem_0061 f) (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0062) (nb056_wpp_notmem_0063 f) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))

noncomputable def nb056_wpp_refl_0022 (f : Var) : TReflOn [((nb056_alpha_dummy_143), (nb056_alpha_dummy_146 f)), ((nb056_alpha_dummy_142), (nb056_alpha_dummy_145 f)), ((nb056_alpha_dummy_141), (nb056_alpha_dummy_144 f)), ((nb056_alpha_dummy_139), (nb056_alpha_dummy_140 f)), ((nb056_alpha_dummy_135), (nb056_alpha_dummy_137 f)), ((nb056_alpha_dummy_136), (nb056_alpha_dummy_138 f)), ((nb056_alpha_dummy_128), (nb056_alpha_dummy_130 f)), ((nb056_alpha_dummy_127), (nb056_alpha_dummy_129 f)), ((nb056_alpha_dummy_133), (nb056_alpha_dummy_134 f)), ((nb056_alpha_dummy_131), (nb056_alpha_dummy_132 f)), ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)), ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)), ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0022 f)

noncomputable def nb056_split_alpha_0015 (f : Var) : TAlphaWff [((nb056_alpha_dummy_143), (nb056_alpha_dummy_146 f)), ((nb056_alpha_dummy_142), (nb056_alpha_dummy_145 f)), ((nb056_alpha_dummy_141), (nb056_alpha_dummy_144 f)), ((nb056_alpha_dummy_139), (nb056_alpha_dummy_140 f)), ((nb056_alpha_dummy_135), (nb056_alpha_dummy_137 f)), ((nb056_alpha_dummy_136), (nb056_alpha_dummy_138 f)), ((nb056_alpha_dummy_128), (nb056_alpha_dummy_130 f)), ((nb056_alpha_dummy_127), (nb056_alpha_dummy_129 f)), ((nb056_alpha_dummy_133), (nb056_alpha_dummy_134 f)), ((nb056_alpha_dummy_131), (nb056_alpha_dummy_132 f)), ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)), ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)), ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb056_alpha_dummy_142)) (Class.cv (nb056_alpha_dummy_143))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_141)) (syn_cun (Class.cv (nb056_alpha_dummy_142)) (Class.cv (nb056_alpha_dummy_143)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb056_alpha_dummy_145 f)) (Class.cv (nb056_alpha_dummy_146 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_144 f)) (syn_cun (Class.cv (nb056_alpha_dummy_145 f)) (Class.cv (nb056_alpha_dummy_146 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0136) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0137 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0134) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0135 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0140) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0141 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0138) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0139 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0136) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0137 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0134) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0135 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0140) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0141 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0138) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0139 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_143), (nb056_alpha_dummy_146 f)), ((nb056_alpha_dummy_142), (nb056_alpha_dummy_145 f)), ((nb056_alpha_dummy_141), (nb056_alpha_dummy_144 f)), ((nb056_alpha_dummy_139), (nb056_alpha_dummy_140 f)), ((nb056_alpha_dummy_135), (nb056_alpha_dummy_137 f)), ((nb056_alpha_dummy_136), (nb056_alpha_dummy_138 f)), ((nb056_alpha_dummy_128), (nb056_alpha_dummy_130 f)), ((nb056_alpha_dummy_127), (nb056_alpha_dummy_129 f)), ((nb056_alpha_dummy_133), (nb056_alpha_dummy_134 f)), ((nb056_alpha_dummy_131), (nb056_alpha_dummy_132 f)), ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)), ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)), ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_c0) (nb056_wpp_refl_0022 f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0144) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0145 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0142) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0143 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0144) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0145 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0142) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0143 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0148) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0149 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0147 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0148) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0149 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0147 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb056_wpp_notmem_0366 : (nb056_alpha_dummy_139) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_139, fv_syn_cnnc] using (nb056_compact_fv_empty_0104)

theorem nb056_wpp_notmem_0367 (f : Var) : (nb056_alpha_dummy_140 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_140, fv_syn_cnnc] using (nb056_compact_fv_empty_0105 f)

theorem nb056_wpp_notmem_0368 : (nb056_alpha_dummy_135) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_135, fv_syn_cnnc] using (nb056_compact_fv_empty_0106)

theorem nb056_wpp_notmem_0369 (f : Var) : (nb056_alpha_dummy_137 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_137, fv_syn_cnnc] using (nb056_compact_fv_empty_0107 f)

theorem nb056_wpp_notmem_0370 : (nb056_alpha_dummy_136) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_136, fv_syn_cnnc] using (nb056_compact_fv_empty_0108)

theorem nb056_wpp_notmem_0371 (f : Var) : (nb056_alpha_dummy_138 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_138, fv_syn_cnnc] using (nb056_compact_fv_empty_0109 f)

theorem nb056_wpp_notmem_0372 : (nb056_alpha_dummy_128) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_128, fv_syn_cnnc] using (nb056_compact_fv_empty_0110)

theorem nb056_wpp_notmem_0373 (f : Var) : (nb056_alpha_dummy_130 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_130, fv_syn_cnnc] using (nb056_compact_fv_empty_0111 f)

theorem nb056_wpp_notmem_0374 : (nb056_alpha_dummy_127) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_127, fv_syn_cnnc] using (nb056_compact_fv_empty_0112)

theorem nb056_wpp_notmem_0375 (f : Var) : (nb056_alpha_dummy_129 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_129, fv_syn_cnnc] using (nb056_compact_fv_empty_0113 f)

theorem nb056_wpp_notmem_0376 : (nb056_alpha_dummy_133) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_133, fv_syn_cnnc] using (nb056_compact_fv_empty_0114)

theorem nb056_wpp_notmem_0377 (f : Var) : (nb056_alpha_dummy_134 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_134, fv_syn_cnnc] using (nb056_compact_fv_empty_0115 f)

theorem nb056_wpp_notmem_0378 : (nb056_alpha_dummy_131) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_131, fv_syn_cnnc] using (nb056_compact_fv_empty_0116)

theorem nb056_wpp_notmem_0379 (f : Var) : (nb056_alpha_dummy_132 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_132, fv_syn_cnnc] using (nb056_compact_fv_empty_0117 f)

theorem nb056_compact_envfresh_0023 (f : Var) : TEnvFresh [((nb056_alpha_dummy_139), (nb056_alpha_dummy_140 f)), ((nb056_alpha_dummy_135), (nb056_alpha_dummy_137 f)), ((nb056_alpha_dummy_136), (nb056_alpha_dummy_138 f)), ((nb056_alpha_dummy_128), (nb056_alpha_dummy_130 f)), ((nb056_alpha_dummy_127), (nb056_alpha_dummy_129 f)), ((nb056_alpha_dummy_133), (nb056_alpha_dummy_134 f)), ((nb056_alpha_dummy_131), (nb056_alpha_dummy_132 f)), ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)), ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)), ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb056_alpha_dummy_139) (nb056_alpha_dummy_140 f) (nb056_wpp_notmem_0366) (nb056_wpp_notmem_0367 f) (TEnvFresh.consFresh (nb056_alpha_dummy_135) (nb056_alpha_dummy_137 f) (nb056_wpp_notmem_0368) (nb056_wpp_notmem_0369 f) (TEnvFresh.consFresh (nb056_alpha_dummy_136) (nb056_alpha_dummy_138 f) (nb056_wpp_notmem_0370) (nb056_wpp_notmem_0371 f) (TEnvFresh.consFresh (nb056_alpha_dummy_128) (nb056_alpha_dummy_130 f) (nb056_wpp_notmem_0372) (nb056_wpp_notmem_0373 f) (TEnvFresh.consFresh (nb056_alpha_dummy_127) (nb056_alpha_dummy_129 f) (nb056_wpp_notmem_0374) (nb056_wpp_notmem_0375 f) (TEnvFresh.consFresh (nb056_alpha_dummy_133) (nb056_alpha_dummy_134 f) (nb056_wpp_notmem_0376) (nb056_wpp_notmem_0377 f) (TEnvFresh.consFresh (nb056_alpha_dummy_131) (nb056_alpha_dummy_132 f) (nb056_wpp_notmem_0378) (nb056_wpp_notmem_0379 f) (TEnvFresh.consFresh (nb056_alpha_dummy_086) (nb056_alpha_dummy_088 f) (nb056_wpp_notmem_0286) (nb056_wpp_notmem_0287 f) (TEnvFresh.consFresh (nb056_alpha_dummy_085) (nb056_alpha_dummy_087 f) (nb056_wpp_notmem_0288) (nb056_wpp_notmem_0289 f) (TEnvFresh.consFresh (nb056_alpha_dummy_089) (nb056_alpha_dummy_090 f) (nb056_wpp_notmem_0290) (nb056_wpp_notmem_0291 f) (TEnvFresh.consFresh (nb056_alpha_dummy_007) (nb056_alpha_dummy_010 f) (nb056_wpp_notmem_0188) (nb056_wpp_notmem_0189 f) (TEnvFresh.consFresh (nb056_alpha_dummy_006) (nb056_alpha_dummy_009 f) (nb056_wpp_notmem_0078) (nb056_wpp_notmem_0079 f) (TEnvFresh.consFresh (nb056_alpha_dummy_005) (nb056_alpha_dummy_008 f) (nb056_wpp_notmem_0080) (nb056_wpp_notmem_0081 f) (TEnvFresh.consFresh (nb056_alpha_dummy_011) (nb056_alpha_dummy_012 f) (nb056_wpp_notmem_0082) (nb056_wpp_notmem_0083 f) (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f) (nb056_wpp_notmem_0084) (nb056_wpp_notmem_0085 f) (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f) (nb056_wpp_notmem_0086) (nb056_wpp_notmem_0087 f) (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0088) (nb056_wpp_notmem_0089 f) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))

noncomputable def nb056_wpp_refl_0023 (f : Var) : TReflOn [((nb056_alpha_dummy_139), (nb056_alpha_dummy_140 f)), ((nb056_alpha_dummy_135), (nb056_alpha_dummy_137 f)), ((nb056_alpha_dummy_136), (nb056_alpha_dummy_138 f)), ((nb056_alpha_dummy_128), (nb056_alpha_dummy_130 f)), ((nb056_alpha_dummy_127), (nb056_alpha_dummy_129 f)), ((nb056_alpha_dummy_133), (nb056_alpha_dummy_134 f)), ((nb056_alpha_dummy_131), (nb056_alpha_dummy_132 f)), ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)), ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)), ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0023 f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
