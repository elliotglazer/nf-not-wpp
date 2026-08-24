import NAR4C061C001Part003

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

noncomputable def nb061_split_alpha_0003 (x : Var) (r : Var) (a : Var) : TAlphaWff [((nb061_alpha_dummy_039), (nb061_alpha_dummy_040 r a)), ((nb061_alpha_dummy_037), (nb061_alpha_dummy_038 r a)), ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)), ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)), ((nb061_alpha_dummy_035), (nb061_alpha_dummy_036 r a)), ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)), ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))] (Wff.imp (Wff.classMem (Class.cv (nb061_alpha_dummy_039)) (syn_cphi (Class.cv (nb061_alpha_dummy_006)))) (Wff.neg (Wff.classMem (Class.cv (nb061_alpha_dummy_039)) (syn_cphi (Class.cv (nb061_alpha_dummy_006)))))) (Wff.imp (Wff.classMem (Class.cv (nb061_alpha_dummy_040 r a)) (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))) (Wff.neg (Wff.classMem (Class.cv (nb061_alpha_dummy_040 r a)) (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0010) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0011 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0010) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0011 r a) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0040) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0041 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0038) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0039 r a) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb061_alpha_dummy_006))).fv) (by decide)) (freshVar_injective (((Class.cv (nb061_alpha_dummy_008 r a))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0014) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0015 r a) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0015 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb061_alpha_dummy_021), (nb061_alpha_dummy_024 r a)), ((nb061_alpha_dummy_020), (nb061_alpha_dummy_023 r a)), ((nb061_alpha_dummy_019), (nb061_alpha_dummy_022 r a)), ((nb061_alpha_dummy_017), (nb061_alpha_dummy_018 r a)), ((nb061_alpha_dummy_013), (nb061_alpha_dummy_015 r a)), ((nb061_alpha_dummy_014), (nb061_alpha_dummy_016 r a)), ((nb061_alpha_dummy_039), (nb061_alpha_dummy_040 r a)), ((nb061_alpha_dummy_037), (nb061_alpha_dummy_038 r a)), ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)), ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)), ((nb061_alpha_dummy_035), (nb061_alpha_dummy_036 r a)), ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)), ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))] (syn_c1c) (nb061_wpp_refl_0003 x r a))) (TAlphaWff.neg (TAlphaWff.neg (nb061_split_alpha_0002 x r a)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb061_alpha_dummy_017), (nb061_alpha_dummy_018 r a)), ((nb061_alpha_dummy_013), (nb061_alpha_dummy_015 r a)), ((nb061_alpha_dummy_014), (nb061_alpha_dummy_016 r a)), ((nb061_alpha_dummy_039), (nb061_alpha_dummy_040 r a)), ((nb061_alpha_dummy_037), (nb061_alpha_dummy_038 r a)), ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)), ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)), ((nb061_alpha_dummy_035), (nb061_alpha_dummy_036 r a)), ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)), ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))] (syn_cnnc) (nb061_wpp_refl_0005 x r a))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb061_alpha_dummy_017), (nb061_alpha_dummy_018 r a)), ((nb061_alpha_dummy_013), (nb061_alpha_dummy_015 r a)), ((nb061_alpha_dummy_014), (nb061_alpha_dummy_016 r a)), ((nb061_alpha_dummy_039), (nb061_alpha_dummy_040 r a)), ((nb061_alpha_dummy_037), (nb061_alpha_dummy_038 r a)), ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)), ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)), ((nb061_alpha_dummy_035), (nb061_alpha_dummy_036 r a)), ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)), ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))] (syn_cnnc) (nb061_wpp_refl_0005 x r a)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0010) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0011 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0010) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0011 r a) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0040) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0041 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0038) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0039 r a) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb061_alpha_dummy_006))).fv) (by decide)) (freshVar_injective (((Class.cv (nb061_alpha_dummy_008 r a))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0014) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0015 r a) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0015 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb061_alpha_dummy_021), (nb061_alpha_dummy_024 r a)), ((nb061_alpha_dummy_020), (nb061_alpha_dummy_023 r a)), ((nb061_alpha_dummy_019), (nb061_alpha_dummy_022 r a)), ((nb061_alpha_dummy_017), (nb061_alpha_dummy_018 r a)), ((nb061_alpha_dummy_013), (nb061_alpha_dummy_015 r a)), ((nb061_alpha_dummy_014), (nb061_alpha_dummy_016 r a)), ((nb061_alpha_dummy_039), (nb061_alpha_dummy_040 r a)), ((nb061_alpha_dummy_037), (nb061_alpha_dummy_038 r a)), ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)), ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)), ((nb061_alpha_dummy_035), (nb061_alpha_dummy_036 r a)), ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)), ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))] (syn_c1c) (nb061_wpp_refl_0003 x r a))) (TAlphaWff.neg (TAlphaWff.neg (nb061_split_alpha_0002 x r a)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb061_alpha_dummy_017), (nb061_alpha_dummy_018 r a)), ((nb061_alpha_dummy_013), (nb061_alpha_dummy_015 r a)), ((nb061_alpha_dummy_014), (nb061_alpha_dummy_016 r a)), ((nb061_alpha_dummy_039), (nb061_alpha_dummy_040 r a)), ((nb061_alpha_dummy_037), (nb061_alpha_dummy_038 r a)), ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)), ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)), ((nb061_alpha_dummy_035), (nb061_alpha_dummy_036 r a)), ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)), ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))] (syn_cnnc) (nb061_wpp_refl_0005 x r a))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb061_alpha_dummy_017), (nb061_alpha_dummy_018 r a)), ((nb061_alpha_dummy_013), (nb061_alpha_dummy_015 r a)), ((nb061_alpha_dummy_014), (nb061_alpha_dummy_016 r a)), ((nb061_alpha_dummy_039), (nb061_alpha_dummy_040 r a)), ((nb061_alpha_dummy_037), (nb061_alpha_dummy_038 r a)), ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)), ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)), ((nb061_alpha_dummy_035), (nb061_alpha_dummy_036 r a)), ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)), ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))] (syn_cnnc) (nb061_wpp_refl_0005 x r a))))))))))))))))))))

theorem nb061_wpp_notmem_0090 : (nb061_alpha_dummy_037) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb061_alpha_dummy_037, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb061_compact_fv_empty_0028)

theorem nb061_wpp_notmem_0091 (r : Var) (a : Var) : (nb061_alpha_dummy_038 r a) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb061_alpha_dummy_038, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb061_compact_fv_empty_0029 r a)

theorem nb061_wpp_notmem_0092 : (nb061_alpha_dummy_006) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb061_alpha_dummy_006, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb061_compact_fv_empty_0012)

theorem nb061_wpp_notmem_0093 (r : Var) (a : Var) : (nb061_alpha_dummy_008 r a) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb061_alpha_dummy_008, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb061_compact_fv_empty_0013 r a)

theorem nb061_wpp_notmem_0094 : (nb061_alpha_dummy_005) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb061_alpha_dummy_005, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb061_compact_fv_empty_0014)

theorem nb061_wpp_notmem_0095 (r : Var) (a : Var) : (nb061_alpha_dummy_007 r a) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb061_alpha_dummy_007, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb061_compact_fv_empty_0015 r a)

theorem nb061_wpp_notmem_0096 : (nb061_alpha_dummy_035) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb061_alpha_dummy_035, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb061_compact_fv_empty_0030)

theorem nb061_wpp_notmem_0097 (r : Var) (a : Var) : (nb061_alpha_dummy_036 r a) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb061_alpha_dummy_036, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb061_compact_fv_empty_0031 r a)

theorem nb061_wpp_notmem_0098 : (nb061_alpha_dummy_009) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb061_alpha_dummy_009, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb061_compact_fv_empty_0018)

theorem nb061_wpp_notmem_0099 (r : Var) (a : Var) : (nb061_alpha_dummy_010 r a) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb061_alpha_dummy_010, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb061_compact_fv_empty_0019 r a)

theorem nb061_wpp_notmem_0100 : (nb061_alpha_dummy_000) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb061_alpha_dummy_000, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb061_compact_fv_empty_0020)

theorem nb061_wpp_notmem_0101 (a : Var) : a ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb061_compact_fv_empty_0021 a)

theorem nb061_wpp_notmem_0102 : (nb061_alpha_dummy_001) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb061_alpha_dummy_001, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb061_compact_fv_empty_0022)

theorem nb061_wpp_notmem_0103 (r : Var) : r ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb061_compact_fv_empty_0023 r)

theorem nb061_wpp_notmem_0104 : (nb061_alpha_dummy_003) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb061_alpha_dummy_003, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb061_compact_fv_empty_0024)

theorem nb061_wpp_notmem_0105 (x : Var) (r : Var) (a : Var) : (nb061_alpha_dummy_004 x r a) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb061_alpha_dummy_004, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb061_compact_fv_empty_0025 x r a)

theorem nb061_compact_envfresh_0006 (x : Var) (r : Var) (a : Var) : TEnvFresh [((nb061_alpha_dummy_037), (nb061_alpha_dummy_038 r a)), ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)), ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)), ((nb061_alpha_dummy_035), (nb061_alpha_dummy_036 r a)), ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)), ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb061_alpha_dummy_037) (nb061_alpha_dummy_038 r a) (nb061_wpp_notmem_0090) (nb061_wpp_notmem_0091 r a) (TEnvFresh.consFresh (nb061_alpha_dummy_006) (nb061_alpha_dummy_008 r a) (nb061_wpp_notmem_0092) (nb061_wpp_notmem_0093 r a) (TEnvFresh.consFresh (nb061_alpha_dummy_005) (nb061_alpha_dummy_007 r a) (nb061_wpp_notmem_0094) (nb061_wpp_notmem_0095 r a) (TEnvFresh.consFresh (nb061_alpha_dummy_035) (nb061_alpha_dummy_036 r a) (nb061_wpp_notmem_0096) (nb061_wpp_notmem_0097 r a) (TEnvFresh.consFresh (nb061_alpha_dummy_009) (nb061_alpha_dummy_010 r a) (nb061_wpp_notmem_0098) (nb061_wpp_notmem_0099 r a) (TEnvFresh.consFresh (nb061_alpha_dummy_000) a (nb061_wpp_notmem_0100) (nb061_wpp_notmem_0101 a) (TEnvFresh.consFresh (nb061_alpha_dummy_001) r (nb061_wpp_notmem_0102) (nb061_wpp_notmem_0103 r) (TEnvFresh.consFresh (nb061_alpha_dummy_003) (nb061_alpha_dummy_004 x r a) (nb061_wpp_notmem_0104) (nb061_wpp_notmem_0105 x r a) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))

noncomputable def nb061_wpp_refl_0006 (x : Var) (r : Var) (a : Var) : TReflOn [((nb061_alpha_dummy_037), (nb061_alpha_dummy_038 r a)), ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)), ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)), ((nb061_alpha_dummy_035), (nb061_alpha_dummy_036 r a)), ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)), ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb061_compact_envfresh_0006 x r a)

noncomputable def nb061_split_alpha_0004 (x : Var) (r : Var) (a : Var) (dv_a_r : a ≠ r) : TAlphaWff [((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))] (Wff.classEq (Class.cv (nb061_alpha_dummy_003)) (syn_cop (Class.cv (nb061_alpha_dummy_001)) (Class.cv (nb061_alpha_dummy_000)))) (Wff.classEq (Class.cv (nb061_alpha_dummy_004 x r a)) (syn_cop (Class.cv r) (Class.cv a))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0002) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0003 x r a) 0))) (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0000) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0001 x r a) 0))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb061_split_alpha_0001 x r a dv_a_r))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb061_split_alpha_0001 x r a dv_a_r))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0032) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0034 r a) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0034 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0036) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0037 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0033) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0035 r a) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb061_alpha_dummy_001))).fv ∪ ((Class.cv (nb061_alpha_dummy_000))).fv) (by decide)) (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb061_split_alpha_0003 x r a))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb061_alpha_dummy_037), (nb061_alpha_dummy_038 r a)), ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)), ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)), ((nb061_alpha_dummy_035), (nb061_alpha_dummy_036 r a)), ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)), ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))] (syn_ccompl (syn_csn (syn_c0c))) (nb061_wpp_refl_0006 x r a))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0032) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0034 r a) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0034 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0036) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0037 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0033) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0035 r a) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb061_alpha_dummy_001))).fv ∪ ((Class.cv (nb061_alpha_dummy_000))).fv) (by decide)) (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb061_split_alpha_0003 x r a))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb061_alpha_dummy_037), (nb061_alpha_dummy_038 r a)), ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)), ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)), ((nb061_alpha_dummy_035), (nb061_alpha_dummy_036 r a)), ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)), ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))] (syn_ccompl (syn_csn (syn_c0c))) (nb061_wpp_refl_0006 x r a)))))))))))))))))))))))))))))

theorem nb061_compact_fv_empty_0032 : (nb061_alpha_dummy_057) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0106 : (nb061_alpha_dummy_057) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_057, fv_syn_c1c] using (nb061_compact_fv_empty_0032)

theorem nb061_compact_fv_empty_0033 (x : Var) : (nb061_alpha_dummy_060 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0107 (x : Var) : (nb061_alpha_dummy_060 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_060, fv_syn_c1c] using (nb061_compact_fv_empty_0033 x)

theorem nb061_compact_fv_empty_0034 : (nb061_alpha_dummy_056) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0108 : (nb061_alpha_dummy_056) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_056, fv_syn_c1c] using (nb061_compact_fv_empty_0034)

theorem nb061_compact_fv_empty_0035 (x : Var) : (nb061_alpha_dummy_059 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0109 (x : Var) : (nb061_alpha_dummy_059 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_059, fv_syn_c1c] using (nb061_compact_fv_empty_0035 x)

theorem nb061_compact_fv_empty_0036 : (nb061_alpha_dummy_055) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0110 : (nb061_alpha_dummy_055) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_055, fv_syn_c1c] using (nb061_compact_fv_empty_0036)

theorem nb061_compact_fv_empty_0037 (x : Var) : (nb061_alpha_dummy_058 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0111 (x : Var) : (nb061_alpha_dummy_058 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_058, fv_syn_c1c] using (nb061_compact_fv_empty_0037 x)

theorem nb061_compact_fv_empty_0038 : (nb061_alpha_dummy_053) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0112 : (nb061_alpha_dummy_053) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_053, fv_syn_c1c] using (nb061_compact_fv_empty_0038)

theorem nb061_compact_fv_empty_0039 (x : Var) : (nb061_alpha_dummy_054 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0113 (x : Var) : (nb061_alpha_dummy_054 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_054, fv_syn_c1c] using (nb061_compact_fv_empty_0039 x)

theorem nb061_compact_fv_empty_0040 : (nb061_alpha_dummy_049) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0114 : (nb061_alpha_dummy_049) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_049, fv_syn_c1c] using (nb061_compact_fv_empty_0040)

theorem nb061_compact_fv_empty_0041 (x : Var) : (nb061_alpha_dummy_051 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0115 (x : Var) : (nb061_alpha_dummy_051 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_051, fv_syn_c1c] using (nb061_compact_fv_empty_0041 x)

theorem nb061_compact_fv_empty_0042 : (nb061_alpha_dummy_050) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0116 : (nb061_alpha_dummy_050) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_050, fv_syn_c1c] using (nb061_compact_fv_empty_0042)

theorem nb061_compact_fv_empty_0043 (x : Var) : (nb061_alpha_dummy_052 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0117 (x : Var) : (nb061_alpha_dummy_052 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_052, fv_syn_c1c] using (nb061_compact_fv_empty_0043 x)

theorem nb061_compact_fv_empty_0044 : (nb061_alpha_dummy_042) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0118 : (nb061_alpha_dummy_042) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_042, fv_syn_c1c] using (nb061_compact_fv_empty_0044)

theorem nb061_compact_fv_empty_0045 (x : Var) : (nb061_alpha_dummy_044 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0119 (x : Var) : (nb061_alpha_dummy_044 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_044, fv_syn_c1c] using (nb061_compact_fv_empty_0045 x)

theorem nb061_compact_fv_empty_0046 : (nb061_alpha_dummy_041) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0120 : (nb061_alpha_dummy_041) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_041, fv_syn_c1c] using (nb061_compact_fv_empty_0046)

theorem nb061_compact_fv_empty_0047 (x : Var) : (nb061_alpha_dummy_043 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0121 (x : Var) : (nb061_alpha_dummy_043 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_043, fv_syn_c1c] using (nb061_compact_fv_empty_0047 x)

theorem nb061_compact_fv_empty_0048 : (nb061_alpha_dummy_047) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0122 : (nb061_alpha_dummy_047) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_047, fv_syn_c1c] using (nb061_compact_fv_empty_0048)

theorem nb061_compact_fv_empty_0049 (x : Var) : (nb061_alpha_dummy_048 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0123 (x : Var) : (nb061_alpha_dummy_048 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_048, fv_syn_c1c] using (nb061_compact_fv_empty_0049 x)

theorem nb061_compact_fv_empty_0050 : (nb061_alpha_dummy_045) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0124 : (nb061_alpha_dummy_045) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_045, fv_syn_c1c] using (nb061_compact_fv_empty_0050)

theorem nb061_compact_fv_empty_0051 (x : Var) : (nb061_alpha_dummy_046 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0125 (x : Var) : (nb061_alpha_dummy_046 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_046, fv_syn_c1c] using (nb061_compact_fv_empty_0051 x)

theorem nb061_compact_fv_empty_0052 : (nb061_alpha_dummy_002) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0126 : (nb061_alpha_dummy_002) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_002, fv_syn_c1c] using (nb061_compact_fv_empty_0052)

theorem nb061_compact_fv_empty_0053 (x : Var) : x ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0127 (x : Var) : x ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb061_compact_fv_empty_0053 x)

theorem nb061_compact_envfresh_0007 (x : Var) (r : Var) (a : Var) : TEnvFresh [((nb061_alpha_dummy_057), (nb061_alpha_dummy_060 x)), ((nb061_alpha_dummy_056), (nb061_alpha_dummy_059 x)), ((nb061_alpha_dummy_055), (nb061_alpha_dummy_058 x)), ((nb061_alpha_dummy_053), (nb061_alpha_dummy_054 x)), ((nb061_alpha_dummy_049), (nb061_alpha_dummy_051 x)), ((nb061_alpha_dummy_050), (nb061_alpha_dummy_052 x)), ((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)), ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)), ((nb061_alpha_dummy_047), (nb061_alpha_dummy_048 x)), ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)), ((nb061_alpha_dummy_002), x), ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb061_alpha_dummy_057) (nb061_alpha_dummy_060 x) (nb061_wpp_notmem_0106) (nb061_wpp_notmem_0107 x) (TEnvFresh.consFresh (nb061_alpha_dummy_056) (nb061_alpha_dummy_059 x) (nb061_wpp_notmem_0108) (nb061_wpp_notmem_0109 x) (TEnvFresh.consFresh (nb061_alpha_dummy_055) (nb061_alpha_dummy_058 x) (nb061_wpp_notmem_0110) (nb061_wpp_notmem_0111 x) (TEnvFresh.consFresh (nb061_alpha_dummy_053) (nb061_alpha_dummy_054 x) (nb061_wpp_notmem_0112) (nb061_wpp_notmem_0113 x) (TEnvFresh.consFresh (nb061_alpha_dummy_049) (nb061_alpha_dummy_051 x) (nb061_wpp_notmem_0114) (nb061_wpp_notmem_0115 x) (TEnvFresh.consFresh (nb061_alpha_dummy_050) (nb061_alpha_dummy_052 x) (nb061_wpp_notmem_0116) (nb061_wpp_notmem_0117 x) (TEnvFresh.consFresh (nb061_alpha_dummy_042) (nb061_alpha_dummy_044 x) (nb061_wpp_notmem_0118) (nb061_wpp_notmem_0119 x) (TEnvFresh.consFresh (nb061_alpha_dummy_041) (nb061_alpha_dummy_043 x) (nb061_wpp_notmem_0120) (nb061_wpp_notmem_0121 x) (TEnvFresh.consFresh (nb061_alpha_dummy_047) (nb061_alpha_dummy_048 x) (nb061_wpp_notmem_0122) (nb061_wpp_notmem_0123 x) (TEnvFresh.consFresh (nb061_alpha_dummy_045) (nb061_alpha_dummy_046 x) (nb061_wpp_notmem_0124) (nb061_wpp_notmem_0125 x) (TEnvFresh.consFresh (nb061_alpha_dummy_002) x (nb061_wpp_notmem_0126) (nb061_wpp_notmem_0127 x) (TEnvFresh.consFresh (nb061_alpha_dummy_000) a (nb061_wpp_notmem_0020) (nb061_wpp_notmem_0021 a) (TEnvFresh.consFresh (nb061_alpha_dummy_001) r (nb061_wpp_notmem_0022) (nb061_wpp_notmem_0023 r) (TEnvFresh.consFresh (nb061_alpha_dummy_003) (nb061_alpha_dummy_004 x r a) (nb061_wpp_notmem_0024) (nb061_wpp_notmem_0025 x r a) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))

noncomputable def nb061_wpp_refl_0007 (x : Var) (r : Var) (a : Var) : TReflOn [((nb061_alpha_dummy_057), (nb061_alpha_dummy_060 x)), ((nb061_alpha_dummy_056), (nb061_alpha_dummy_059 x)), ((nb061_alpha_dummy_055), (nb061_alpha_dummy_058 x)), ((nb061_alpha_dummy_053), (nb061_alpha_dummy_054 x)), ((nb061_alpha_dummy_049), (nb061_alpha_dummy_051 x)), ((nb061_alpha_dummy_050), (nb061_alpha_dummy_052 x)), ((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)), ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)), ((nb061_alpha_dummy_047), (nb061_alpha_dummy_048 x)), ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)), ((nb061_alpha_dummy_002), x), ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb061_compact_envfresh_0007 x r a)

theorem nb061_wpp_notmem_0128 : (nb061_alpha_dummy_057) ∉ ((syn_c0)).fv := by
  simpa only [nb061_alpha_dummy_057, fv_syn_c0] using (nb061_compact_fv_empty_0032)

theorem nb061_wpp_notmem_0129 (x : Var) : (nb061_alpha_dummy_060 x) ∉ ((syn_c0)).fv := by
  simpa only [nb061_alpha_dummy_060, fv_syn_c0] using (nb061_compact_fv_empty_0033 x)

theorem nb061_wpp_notmem_0130 : (nb061_alpha_dummy_056) ∉ ((syn_c0)).fv := by
  simpa only [nb061_alpha_dummy_056, fv_syn_c0] using (nb061_compact_fv_empty_0034)

theorem nb061_wpp_notmem_0131 (x : Var) : (nb061_alpha_dummy_059 x) ∉ ((syn_c0)).fv := by
  simpa only [nb061_alpha_dummy_059, fv_syn_c0] using (nb061_compact_fv_empty_0035 x)

theorem nb061_wpp_notmem_0132 : (nb061_alpha_dummy_055) ∉ ((syn_c0)).fv := by
  simpa only [nb061_alpha_dummy_055, fv_syn_c0] using (nb061_compact_fv_empty_0036)

theorem nb061_wpp_notmem_0133 (x : Var) : (nb061_alpha_dummy_058 x) ∉ ((syn_c0)).fv := by
  simpa only [nb061_alpha_dummy_058, fv_syn_c0] using (nb061_compact_fv_empty_0037 x)

theorem nb061_wpp_notmem_0134 : (nb061_alpha_dummy_053) ∉ ((syn_c0)).fv := by
  simpa only [nb061_alpha_dummy_053, fv_syn_c0] using (nb061_compact_fv_empty_0038)

theorem nb061_wpp_notmem_0135 (x : Var) : (nb061_alpha_dummy_054 x) ∉ ((syn_c0)).fv := by
  simpa only [nb061_alpha_dummy_054, fv_syn_c0] using (nb061_compact_fv_empty_0039 x)

theorem nb061_wpp_notmem_0136 : (nb061_alpha_dummy_049) ∉ ((syn_c0)).fv := by
  simpa only [nb061_alpha_dummy_049, fv_syn_c0] using (nb061_compact_fv_empty_0040)

theorem nb061_wpp_notmem_0137 (x : Var) : (nb061_alpha_dummy_051 x) ∉ ((syn_c0)).fv := by
  simpa only [nb061_alpha_dummy_051, fv_syn_c0] using (nb061_compact_fv_empty_0041 x)

theorem nb061_wpp_notmem_0138 : (nb061_alpha_dummy_050) ∉ ((syn_c0)).fv := by
  simpa only [nb061_alpha_dummy_050, fv_syn_c0] using (nb061_compact_fv_empty_0042)

theorem nb061_wpp_notmem_0139 (x : Var) : (nb061_alpha_dummy_052 x) ∉ ((syn_c0)).fv := by
  simpa only [nb061_alpha_dummy_052, fv_syn_c0] using (nb061_compact_fv_empty_0043 x)

theorem nb061_wpp_notmem_0140 : (nb061_alpha_dummy_042) ∉ ((syn_c0)).fv := by
  simpa only [nb061_alpha_dummy_042, fv_syn_c0] using (nb061_compact_fv_empty_0044)

theorem nb061_wpp_notmem_0141 (x : Var) : (nb061_alpha_dummy_044 x) ∉ ((syn_c0)).fv := by
  simpa only [nb061_alpha_dummy_044, fv_syn_c0] using (nb061_compact_fv_empty_0045 x)

theorem nb061_wpp_notmem_0142 : (nb061_alpha_dummy_041) ∉ ((syn_c0)).fv := by
  simpa only [nb061_alpha_dummy_041, fv_syn_c0] using (nb061_compact_fv_empty_0046)

theorem nb061_wpp_notmem_0143 (x : Var) : (nb061_alpha_dummy_043 x) ∉ ((syn_c0)).fv := by
  simpa only [nb061_alpha_dummy_043, fv_syn_c0] using (nb061_compact_fv_empty_0047 x)

theorem nb061_wpp_notmem_0144 : (nb061_alpha_dummy_047) ∉ ((syn_c0)).fv := by
  simpa only [nb061_alpha_dummy_047, fv_syn_c0] using (nb061_compact_fv_empty_0048)

theorem nb061_wpp_notmem_0145 (x : Var) : (nb061_alpha_dummy_048 x) ∉ ((syn_c0)).fv := by
  simpa only [nb061_alpha_dummy_048, fv_syn_c0] using (nb061_compact_fv_empty_0049 x)

theorem nb061_wpp_notmem_0146 : (nb061_alpha_dummy_045) ∉ ((syn_c0)).fv := by
  simpa only [nb061_alpha_dummy_045, fv_syn_c0] using (nb061_compact_fv_empty_0050)

theorem nb061_wpp_notmem_0147 (x : Var) : (nb061_alpha_dummy_046 x) ∉ ((syn_c0)).fv := by
  simpa only [nb061_alpha_dummy_046, fv_syn_c0] using (nb061_compact_fv_empty_0051 x)

theorem nb061_wpp_notmem_0148 : (nb061_alpha_dummy_002) ∉ ((syn_c0)).fv := by
  simpa only [nb061_alpha_dummy_002, fv_syn_c0] using (nb061_compact_fv_empty_0052)

theorem nb061_wpp_notmem_0149 (x : Var) : x ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb061_compact_fv_empty_0053 x)

theorem nb061_compact_envfresh_0008 (x : Var) (r : Var) (a : Var) : TEnvFresh [((nb061_alpha_dummy_057), (nb061_alpha_dummy_060 x)), ((nb061_alpha_dummy_056), (nb061_alpha_dummy_059 x)), ((nb061_alpha_dummy_055), (nb061_alpha_dummy_058 x)), ((nb061_alpha_dummy_053), (nb061_alpha_dummy_054 x)), ((nb061_alpha_dummy_049), (nb061_alpha_dummy_051 x)), ((nb061_alpha_dummy_050), (nb061_alpha_dummy_052 x)), ((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)), ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)), ((nb061_alpha_dummy_047), (nb061_alpha_dummy_048 x)), ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)), ((nb061_alpha_dummy_002), x), ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb061_alpha_dummy_057) (nb061_alpha_dummy_060 x) (nb061_wpp_notmem_0128) (nb061_wpp_notmem_0129 x) (TEnvFresh.consFresh (nb061_alpha_dummy_056) (nb061_alpha_dummy_059 x) (nb061_wpp_notmem_0130) (nb061_wpp_notmem_0131 x) (TEnvFresh.consFresh (nb061_alpha_dummy_055) (nb061_alpha_dummy_058 x) (nb061_wpp_notmem_0132) (nb061_wpp_notmem_0133 x) (TEnvFresh.consFresh (nb061_alpha_dummy_053) (nb061_alpha_dummy_054 x) (nb061_wpp_notmem_0134) (nb061_wpp_notmem_0135 x) (TEnvFresh.consFresh (nb061_alpha_dummy_049) (nb061_alpha_dummy_051 x) (nb061_wpp_notmem_0136) (nb061_wpp_notmem_0137 x) (TEnvFresh.consFresh (nb061_alpha_dummy_050) (nb061_alpha_dummy_052 x) (nb061_wpp_notmem_0138) (nb061_wpp_notmem_0139 x) (TEnvFresh.consFresh (nb061_alpha_dummy_042) (nb061_alpha_dummy_044 x) (nb061_wpp_notmem_0140) (nb061_wpp_notmem_0141 x) (TEnvFresh.consFresh (nb061_alpha_dummy_041) (nb061_alpha_dummy_043 x) (nb061_wpp_notmem_0142) (nb061_wpp_notmem_0143 x) (TEnvFresh.consFresh (nb061_alpha_dummy_047) (nb061_alpha_dummy_048 x) (nb061_wpp_notmem_0144) (nb061_wpp_notmem_0145 x) (TEnvFresh.consFresh (nb061_alpha_dummy_045) (nb061_alpha_dummy_046 x) (nb061_wpp_notmem_0146) (nb061_wpp_notmem_0147 x) (TEnvFresh.consFresh (nb061_alpha_dummy_002) x (nb061_wpp_notmem_0148) (nb061_wpp_notmem_0149 x) (TEnvFresh.consFresh (nb061_alpha_dummy_000) a (nb061_wpp_notmem_0046) (nb061_wpp_notmem_0047 a) (TEnvFresh.consFresh (nb061_alpha_dummy_001) r (nb061_wpp_notmem_0048) (nb061_wpp_notmem_0049 r) (TEnvFresh.consFresh (nb061_alpha_dummy_003) (nb061_alpha_dummy_004 x r a) (nb061_wpp_notmem_0050) (nb061_wpp_notmem_0051 x r a) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))

noncomputable def nb061_wpp_refl_0008 (x : Var) (r : Var) (a : Var) : TReflOn [((nb061_alpha_dummy_057), (nb061_alpha_dummy_060 x)), ((nb061_alpha_dummy_056), (nb061_alpha_dummy_059 x)), ((nb061_alpha_dummy_055), (nb061_alpha_dummy_058 x)), ((nb061_alpha_dummy_053), (nb061_alpha_dummy_054 x)), ((nb061_alpha_dummy_049), (nb061_alpha_dummy_051 x)), ((nb061_alpha_dummy_050), (nb061_alpha_dummy_052 x)), ((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)), ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)), ((nb061_alpha_dummy_047), (nb061_alpha_dummy_048 x)), ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)), ((nb061_alpha_dummy_002), x), ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb061_compact_envfresh_0008 x r a)

noncomputable def nb061_split_alpha_0005 (x : Var) (r : Var) (a : Var) : TAlphaWff [((nb061_alpha_dummy_057), (nb061_alpha_dummy_060 x)), ((nb061_alpha_dummy_056), (nb061_alpha_dummy_059 x)), ((nb061_alpha_dummy_055), (nb061_alpha_dummy_058 x)), ((nb061_alpha_dummy_053), (nb061_alpha_dummy_054 x)), ((nb061_alpha_dummy_049), (nb061_alpha_dummy_051 x)), ((nb061_alpha_dummy_050), (nb061_alpha_dummy_052 x)), ((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)), ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)), ((nb061_alpha_dummy_047), (nb061_alpha_dummy_048 x)), ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)), ((nb061_alpha_dummy_002), x), ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb061_alpha_dummy_056)) (Class.cv (nb061_alpha_dummy_057))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb061_alpha_dummy_055)) (syn_cun (Class.cv (nb061_alpha_dummy_056)) (Class.cv (nb061_alpha_dummy_057)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb061_alpha_dummy_059 x)) (Class.cv (nb061_alpha_dummy_060 x))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb061_alpha_dummy_058 x)) (syn_cun (Class.cv (nb061_alpha_dummy_059 x)) (Class.cv (nb061_alpha_dummy_060 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0057 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0055 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0061 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0059 x) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0057 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0055 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0061 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0059 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb061_alpha_dummy_057), (nb061_alpha_dummy_060 x)), ((nb061_alpha_dummy_056), (nb061_alpha_dummy_059 x)), ((nb061_alpha_dummy_055), (nb061_alpha_dummy_058 x)), ((nb061_alpha_dummy_053), (nb061_alpha_dummy_054 x)), ((nb061_alpha_dummy_049), (nb061_alpha_dummy_051 x)), ((nb061_alpha_dummy_050), (nb061_alpha_dummy_052 x)), ((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)), ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)), ((nb061_alpha_dummy_047), (nb061_alpha_dummy_048 x)), ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)), ((nb061_alpha_dummy_002), x), ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))] (syn_c0) (nb061_wpp_refl_0008 x r a))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0065 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0063 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0065 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0063 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0069 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0067 x) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0069 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0067 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb061_wpp_notmem_0150 : (nb061_alpha_dummy_053) ∉ ((syn_cnnc)).fv := by
  simpa only [nb061_alpha_dummy_053, fv_syn_cnnc] using (nb061_compact_fv_empty_0038)

theorem nb061_wpp_notmem_0151 (x : Var) : (nb061_alpha_dummy_054 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb061_alpha_dummy_054, fv_syn_cnnc] using (nb061_compact_fv_empty_0039 x)

theorem nb061_wpp_notmem_0152 : (nb061_alpha_dummy_049) ∉ ((syn_cnnc)).fv := by
  simpa only [nb061_alpha_dummy_049, fv_syn_cnnc] using (nb061_compact_fv_empty_0040)

theorem nb061_wpp_notmem_0153 (x : Var) : (nb061_alpha_dummy_051 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb061_alpha_dummy_051, fv_syn_cnnc] using (nb061_compact_fv_empty_0041 x)

theorem nb061_wpp_notmem_0154 : (nb061_alpha_dummy_050) ∉ ((syn_cnnc)).fv := by
  simpa only [nb061_alpha_dummy_050, fv_syn_cnnc] using (nb061_compact_fv_empty_0042)

theorem nb061_wpp_notmem_0155 (x : Var) : (nb061_alpha_dummy_052 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb061_alpha_dummy_052, fv_syn_cnnc] using (nb061_compact_fv_empty_0043 x)

theorem nb061_wpp_notmem_0156 : (nb061_alpha_dummy_042) ∉ ((syn_cnnc)).fv := by
  simpa only [nb061_alpha_dummy_042, fv_syn_cnnc] using (nb061_compact_fv_empty_0044)

theorem nb061_wpp_notmem_0157 (x : Var) : (nb061_alpha_dummy_044 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb061_alpha_dummy_044, fv_syn_cnnc] using (nb061_compact_fv_empty_0045 x)

theorem nb061_wpp_notmem_0158 : (nb061_alpha_dummy_041) ∉ ((syn_cnnc)).fv := by
  simpa only [nb061_alpha_dummy_041, fv_syn_cnnc] using (nb061_compact_fv_empty_0046)

theorem nb061_wpp_notmem_0159 (x : Var) : (nb061_alpha_dummy_043 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb061_alpha_dummy_043, fv_syn_cnnc] using (nb061_compact_fv_empty_0047 x)

theorem nb061_wpp_notmem_0160 : (nb061_alpha_dummy_047) ∉ ((syn_cnnc)).fv := by
  simpa only [nb061_alpha_dummy_047, fv_syn_cnnc] using (nb061_compact_fv_empty_0048)

theorem nb061_wpp_notmem_0161 (x : Var) : (nb061_alpha_dummy_048 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb061_alpha_dummy_048, fv_syn_cnnc] using (nb061_compact_fv_empty_0049 x)

theorem nb061_wpp_notmem_0162 : (nb061_alpha_dummy_045) ∉ ((syn_cnnc)).fv := by
  simpa only [nb061_alpha_dummy_045, fv_syn_cnnc] using (nb061_compact_fv_empty_0050)

theorem nb061_wpp_notmem_0163 (x : Var) : (nb061_alpha_dummy_046 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb061_alpha_dummy_046, fv_syn_cnnc] using (nb061_compact_fv_empty_0051 x)

theorem nb061_wpp_notmem_0164 : (nb061_alpha_dummy_002) ∉ ((syn_cnnc)).fv := by
  simpa only [nb061_alpha_dummy_002, fv_syn_cnnc] using (nb061_compact_fv_empty_0052)

theorem nb061_wpp_notmem_0165 (x : Var) : x ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb061_compact_fv_empty_0053 x)

theorem nb061_compact_envfresh_0009 (x : Var) (r : Var) (a : Var) : TEnvFresh [((nb061_alpha_dummy_053), (nb061_alpha_dummy_054 x)), ((nb061_alpha_dummy_049), (nb061_alpha_dummy_051 x)), ((nb061_alpha_dummy_050), (nb061_alpha_dummy_052 x)), ((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)), ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)), ((nb061_alpha_dummy_047), (nb061_alpha_dummy_048 x)), ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)), ((nb061_alpha_dummy_002), x), ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb061_alpha_dummy_053) (nb061_alpha_dummy_054 x) (nb061_wpp_notmem_0150) (nb061_wpp_notmem_0151 x) (TEnvFresh.consFresh (nb061_alpha_dummy_049) (nb061_alpha_dummy_051 x) (nb061_wpp_notmem_0152) (nb061_wpp_notmem_0153 x) (TEnvFresh.consFresh (nb061_alpha_dummy_050) (nb061_alpha_dummy_052 x) (nb061_wpp_notmem_0154) (nb061_wpp_notmem_0155 x) (TEnvFresh.consFresh (nb061_alpha_dummy_042) (nb061_alpha_dummy_044 x) (nb061_wpp_notmem_0156) (nb061_wpp_notmem_0157 x) (TEnvFresh.consFresh (nb061_alpha_dummy_041) (nb061_alpha_dummy_043 x) (nb061_wpp_notmem_0158) (nb061_wpp_notmem_0159 x) (TEnvFresh.consFresh (nb061_alpha_dummy_047) (nb061_alpha_dummy_048 x) (nb061_wpp_notmem_0160) (nb061_wpp_notmem_0161 x) (TEnvFresh.consFresh (nb061_alpha_dummy_045) (nb061_alpha_dummy_046 x) (nb061_wpp_notmem_0162) (nb061_wpp_notmem_0163 x) (TEnvFresh.consFresh (nb061_alpha_dummy_002) x (nb061_wpp_notmem_0164) (nb061_wpp_notmem_0165 x) (TEnvFresh.consFresh (nb061_alpha_dummy_000) a (nb061_wpp_notmem_0066) (nb061_wpp_notmem_0067 a) (TEnvFresh.consFresh (nb061_alpha_dummy_001) r (nb061_wpp_notmem_0068) (nb061_wpp_notmem_0069 r) (TEnvFresh.consFresh (nb061_alpha_dummy_003) (nb061_alpha_dummy_004 x r a) (nb061_wpp_notmem_0070) (nb061_wpp_notmem_0071 x r a) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))

noncomputable def nb061_wpp_refl_0009 (x : Var) (r : Var) (a : Var) : TReflOn [((nb061_alpha_dummy_053), (nb061_alpha_dummy_054 x)), ((nb061_alpha_dummy_049), (nb061_alpha_dummy_051 x)), ((nb061_alpha_dummy_050), (nb061_alpha_dummy_052 x)), ((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)), ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)), ((nb061_alpha_dummy_047), (nb061_alpha_dummy_048 x)), ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)), ((nb061_alpha_dummy_002), x), ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb061_compact_envfresh_0009 x r a)

noncomputable def nb061_split_alpha_0006 (x : Var) (r : Var) (a : Var) : TAlphaWff [((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)), ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)), ((nb061_alpha_dummy_047), (nb061_alpha_dummy_048 x)), ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)), ((nb061_alpha_dummy_002), x), ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))] (Wff.imp (Wff.classMem (Class.cv (nb061_alpha_dummy_042)) (Class.cv (nb061_alpha_dummy_002))) (Wff.neg (Wff.classEq (Class.cv (nb061_alpha_dummy_041)) (syn_cphi (Class.cv (nb061_alpha_dummy_042)))))) (Wff.imp (Wff.classMem (Class.cv (nb061_alpha_dummy_044 x)) (Class.cv x)) (Wff.neg (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x)) (syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0042) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0044 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0042) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0044 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0046) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0047 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0043) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0045 x) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb061_alpha_dummy_002))).fv ∪ ((Class.cv (nb061_alpha_dummy_002))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv x)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0048) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0049 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0048) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0049 x) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb061_alpha_dummy_042))).fv) (by decide)) (freshVar_injective (((Class.cv (nb061_alpha_dummy_044 x))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0052) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0053 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0052) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0053 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0051 x) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb061_alpha_dummy_057), (nb061_alpha_dummy_060 x)), ((nb061_alpha_dummy_056), (nb061_alpha_dummy_059 x)), ((nb061_alpha_dummy_055), (nb061_alpha_dummy_058 x)), ((nb061_alpha_dummy_053), (nb061_alpha_dummy_054 x)), ((nb061_alpha_dummy_049), (nb061_alpha_dummy_051 x)), ((nb061_alpha_dummy_050), (nb061_alpha_dummy_052 x)), ((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)), ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)), ((nb061_alpha_dummy_047), (nb061_alpha_dummy_048 x)), ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)), ((nb061_alpha_dummy_002), x), ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))] (syn_c1c) (nb061_wpp_refl_0007 x r a))) (TAlphaWff.neg (TAlphaWff.neg (nb061_split_alpha_0005 x r a)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0051 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb061_alpha_dummy_053), (nb061_alpha_dummy_054 x)), ((nb061_alpha_dummy_049), (nb061_alpha_dummy_051 x)), ((nb061_alpha_dummy_050), (nb061_alpha_dummy_052 x)), ((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)), ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)), ((nb061_alpha_dummy_047), (nb061_alpha_dummy_048 x)), ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)), ((nb061_alpha_dummy_002), x), ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))] (syn_cnnc) (nb061_wpp_refl_0009 x r a))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0051 x) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0051 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb061_alpha_dummy_053), (nb061_alpha_dummy_054 x)), ((nb061_alpha_dummy_049), (nb061_alpha_dummy_051 x)), ((nb061_alpha_dummy_050), (nb061_alpha_dummy_052 x)), ((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)), ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)), ((nb061_alpha_dummy_047), (nb061_alpha_dummy_048 x)), ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)), ((nb061_alpha_dummy_002), x), ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))] (syn_cnnc) (nb061_wpp_refl_0009 x r a))))))))))))))))))))

theorem nb061_compact_fv_empty_0054 : (nb061_alpha_dummy_075) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0166 : (nb061_alpha_dummy_075) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_075, fv_syn_c1c] using (nb061_compact_fv_empty_0054)

theorem nb061_compact_fv_empty_0055 (x : Var) : (nb061_alpha_dummy_076 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0167 (x : Var) : (nb061_alpha_dummy_076 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_076, fv_syn_c1c] using (nb061_compact_fv_empty_0055 x)

theorem nb061_compact_fv_empty_0056 : (nb061_alpha_dummy_073) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0168 : (nb061_alpha_dummy_073) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_073, fv_syn_c1c] using (nb061_compact_fv_empty_0056)

theorem nb061_compact_fv_empty_0057 (x : Var) : (nb061_alpha_dummy_074 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0169 (x : Var) : (nb061_alpha_dummy_074 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_074, fv_syn_c1c] using (nb061_compact_fv_empty_0057 x)

theorem nb061_compact_fv_empty_0058 : (nb061_alpha_dummy_071) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0170 : (nb061_alpha_dummy_071) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_071, fv_syn_c1c] using (nb061_compact_fv_empty_0058)

theorem nb061_compact_fv_empty_0059 (x : Var) : (nb061_alpha_dummy_072 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb061_wpp_notmem_0171 (x : Var) : (nb061_alpha_dummy_072 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb061_alpha_dummy_072, fv_syn_c1c] using (nb061_compact_fv_empty_0059 x)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
