import NAR4C064C001Part003

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

noncomputable def nb064_split_alpha_0003 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TAlphaWff [((nb064_alpha_dummy_041), (nb064_alpha_dummy_042 r a)), ((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] (Wff.imp (Wff.classMem (Class.cv (nb064_alpha_dummy_041)) (syn_cphi (Class.cv (nb064_alpha_dummy_008)))) (Wff.neg (Wff.classMem (Class.cv (nb064_alpha_dummy_041)) (syn_cphi (Class.cv (nb064_alpha_dummy_008)))))) (Wff.imp (Wff.classMem (Class.cv (nb064_alpha_dummy_042 r a)) (syn_cphi (Class.cv (nb064_alpha_dummy_010 r a)))) (Wff.neg (Wff.classMem (Class.cv (nb064_alpha_dummy_042 r a)) (syn_cphi (Class.cv (nb064_alpha_dummy_010 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0010) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0011 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0010) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0011 r a) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0040) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0041 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0038) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0039 r a) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_008))).fv) (by decide)) (freshVar_injective (((Class.cv (nb064_alpha_dummy_010 r a))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0014) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0015 r a) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0015 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb064_alpha_dummy_023), (nb064_alpha_dummy_026 r a)), ((nb064_alpha_dummy_022), (nb064_alpha_dummy_025 r a)), ((nb064_alpha_dummy_021), (nb064_alpha_dummy_024 r a)), ((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_041), (nb064_alpha_dummy_042 r a)), ((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] (syn_c1c) (nb064_wpp_refl_0003 x y z r a))) (TAlphaWff.neg (TAlphaWff.neg (nb064_split_alpha_0002 x y z r a)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_041), (nb064_alpha_dummy_042 r a)), ((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] (syn_cnnc) (nb064_wpp_refl_0005 x y z r a))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_041), (nb064_alpha_dummy_042 r a)), ((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] (syn_cnnc) (nb064_wpp_refl_0005 x y z r a)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0010) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0011 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0010) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0011 r a) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0040) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0041 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0038) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0039 r a) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_008))).fv) (by decide)) (freshVar_injective (((Class.cv (nb064_alpha_dummy_010 r a))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0014) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0015 r a) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0015 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb064_alpha_dummy_023), (nb064_alpha_dummy_026 r a)), ((nb064_alpha_dummy_022), (nb064_alpha_dummy_025 r a)), ((nb064_alpha_dummy_021), (nb064_alpha_dummy_024 r a)), ((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_041), (nb064_alpha_dummy_042 r a)), ((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] (syn_c1c) (nb064_wpp_refl_0003 x y z r a))) (TAlphaWff.neg (TAlphaWff.neg (nb064_split_alpha_0002 x y z r a)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_041), (nb064_alpha_dummy_042 r a)), ((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] (syn_cnnc) (nb064_wpp_refl_0005 x y z r a))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)), ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_041), (nb064_alpha_dummy_042 r a)), ((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] (syn_cnnc) (nb064_wpp_refl_0005 x y z r a))))))))))))))))))))

theorem nb064_wpp_notmem_0090 : (nb064_alpha_dummy_039) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb064_alpha_dummy_039, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb064_compact_fv_empty_0028)

theorem nb064_wpp_notmem_0091 (r : Var) (a : Var) : (nb064_alpha_dummy_040 r a) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb064_alpha_dummy_040, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb064_compact_fv_empty_0029 r a)

theorem nb064_wpp_notmem_0092 : (nb064_alpha_dummy_008) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb064_alpha_dummy_008, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb064_compact_fv_empty_0012)

theorem nb064_wpp_notmem_0093 (r : Var) (a : Var) : (nb064_alpha_dummy_010 r a) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb064_alpha_dummy_010, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb064_compact_fv_empty_0013 r a)

theorem nb064_wpp_notmem_0094 : (nb064_alpha_dummy_007) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb064_alpha_dummy_007, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb064_compact_fv_empty_0014)

theorem nb064_wpp_notmem_0095 (r : Var) (a : Var) : (nb064_alpha_dummy_009 r a) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb064_alpha_dummy_009, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb064_compact_fv_empty_0015 r a)

theorem nb064_wpp_notmem_0096 : (nb064_alpha_dummy_037) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb064_alpha_dummy_037, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb064_compact_fv_empty_0030)

theorem nb064_wpp_notmem_0097 (r : Var) (a : Var) : (nb064_alpha_dummy_038 r a) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb064_alpha_dummy_038, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb064_compact_fv_empty_0031 r a)

theorem nb064_wpp_notmem_0098 : (nb064_alpha_dummy_011) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb064_alpha_dummy_011, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb064_compact_fv_empty_0018)

theorem nb064_wpp_notmem_0099 (r : Var) (a : Var) : (nb064_alpha_dummy_012 r a) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb064_alpha_dummy_012, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb064_compact_fv_empty_0019 r a)

theorem nb064_wpp_notmem_0100 : (nb064_alpha_dummy_000) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb064_alpha_dummy_000, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb064_compact_fv_empty_0020)

theorem nb064_wpp_notmem_0101 (a : Var) : a ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb064_compact_fv_empty_0021 a)

theorem nb064_wpp_notmem_0102 : (nb064_alpha_dummy_001) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb064_alpha_dummy_001, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb064_compact_fv_empty_0022)

theorem nb064_wpp_notmem_0103 (r : Var) : r ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb064_compact_fv_empty_0023 r)

theorem nb064_wpp_notmem_0104 : (nb064_alpha_dummy_005) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb064_alpha_dummy_005, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb064_compact_fv_empty_0024)

theorem nb064_wpp_notmem_0105 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : (nb064_alpha_dummy_006 x y z r a) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb064_alpha_dummy_006, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb064_compact_fv_empty_0025 x y z r a)

theorem nb064_compact_envfresh_0006 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb064_alpha_dummy_039) (nb064_alpha_dummy_040 r a) (nb064_wpp_notmem_0090) (nb064_wpp_notmem_0091 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_008) (nb064_alpha_dummy_010 r a) (nb064_wpp_notmem_0092) (nb064_wpp_notmem_0093 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_007) (nb064_alpha_dummy_009 r a) (nb064_wpp_notmem_0094) (nb064_wpp_notmem_0095 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_037) (nb064_alpha_dummy_038 r a) (nb064_wpp_notmem_0096) (nb064_wpp_notmem_0097 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_011) (nb064_alpha_dummy_012 r a) (nb064_wpp_notmem_0098) (nb064_wpp_notmem_0099 r a) (TEnvFresh.consFresh (nb064_alpha_dummy_000) a (nb064_wpp_notmem_0100) (nb064_wpp_notmem_0101 a) (TEnvFresh.consFresh (nb064_alpha_dummy_001) r (nb064_wpp_notmem_0102) (nb064_wpp_notmem_0103 r) (TEnvFresh.consFresh (nb064_alpha_dummy_005) (nb064_alpha_dummy_006 x y z r a) (nb064_wpp_notmem_0104) (nb064_wpp_notmem_0105 x y z r a) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))

noncomputable def nb064_wpp_refl_0006 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb064_compact_envfresh_0006 x y z r a)

noncomputable def nb064_split_alpha_0004 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) (dv_a_r : a ≠ r) : TAlphaWff [((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] (Wff.classEq (Class.cv (nb064_alpha_dummy_005)) (syn_cop (Class.cv (nb064_alpha_dummy_001)) (Class.cv (nb064_alpha_dummy_000)))) (Wff.classEq (Class.cv (nb064_alpha_dummy_006 x y z r a)) (syn_cop (Class.cv r) (Class.cv a))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0002) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0003 x y z r a) 0))) (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0000) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0001 x y z r a) 0))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb064_split_alpha_0001 x y z r a dv_a_r))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb064_split_alpha_0001 x y z r a dv_a_r))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0032) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0034 r a) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0034 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0036) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0037 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0033) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0035 r a) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_001))).fv ∪ ((Class.cv (nb064_alpha_dummy_000))).fv) (by decide)) (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb064_split_alpha_0003 x y z r a))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] (syn_ccompl (syn_csn (syn_c0c))) (nb064_wpp_refl_0006 x y z r a))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0032) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0034 r a) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0034 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0036) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0037 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0033) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0035 r a) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_001))).fv ∪ ((Class.cv (nb064_alpha_dummy_000))).fv) (by decide)) (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb064_split_alpha_0003 x y z r a))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)), ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] (syn_ccompl (syn_csn (syn_c0c))) (nb064_wpp_refl_0006 x y z r a)))))))))))))))))))))))))))))

theorem nb064_compact_fv_empty_0032 : (nb064_alpha_dummy_002) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0106 : (nb064_alpha_dummy_002) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_002, fv_syn_c0] using (nb064_compact_fv_empty_0032)

theorem nb064_compact_fv_empty_0033 (x : Var) : x ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0107 (x : Var) : x ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb064_compact_fv_empty_0033 x)

theorem nb064_compact_envfresh_0007 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb064_alpha_dummy_002) x (nb064_wpp_notmem_0106) (nb064_wpp_notmem_0107 x) (TEnvFresh.consFresh (nb064_alpha_dummy_000) a (nb064_wpp_notmem_0046) (nb064_wpp_notmem_0047 a) (TEnvFresh.consFresh (nb064_alpha_dummy_001) r (nb064_wpp_notmem_0048) (nb064_wpp_notmem_0049 r) (TEnvFresh.consFresh (nb064_alpha_dummy_005) (nb064_alpha_dummy_006 x y z r a) (nb064_wpp_notmem_0050) (nb064_wpp_notmem_0051 x y z r a) (TEnvFresh.nil ((syn_c0)).fv)))))

noncomputable def nb064_wpp_refl_0007 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb064_compact_envfresh_0007 x y z r a)

theorem nb064_compact_fv_empty_0034 : (nb064_alpha_dummy_063) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0108 : (nb064_alpha_dummy_063) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_063, fv_syn_c1c] using (nb064_compact_fv_empty_0034)

theorem nb064_compact_fv_empty_0035 (y : Var) (z : Var) : (nb064_alpha_dummy_066 y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0109 (y : Var) (z : Var) : (nb064_alpha_dummy_066 y z) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_066, fv_syn_c1c] using (nb064_compact_fv_empty_0035 y z)

theorem nb064_compact_fv_empty_0036 : (nb064_alpha_dummy_062) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0110 : (nb064_alpha_dummy_062) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_062, fv_syn_c1c] using (nb064_compact_fv_empty_0036)

theorem nb064_compact_fv_empty_0037 (y : Var) (z : Var) : (nb064_alpha_dummy_065 y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0111 (y : Var) (z : Var) : (nb064_alpha_dummy_065 y z) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_065, fv_syn_c1c] using (nb064_compact_fv_empty_0037 y z)

theorem nb064_compact_fv_empty_0038 : (nb064_alpha_dummy_061) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0112 : (nb064_alpha_dummy_061) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_061, fv_syn_c1c] using (nb064_compact_fv_empty_0038)

theorem nb064_compact_fv_empty_0039 (y : Var) (z : Var) : (nb064_alpha_dummy_064 y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0113 (y : Var) (z : Var) : (nb064_alpha_dummy_064 y z) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_064, fv_syn_c1c] using (nb064_compact_fv_empty_0039 y z)

theorem nb064_compact_fv_empty_0040 : (nb064_alpha_dummy_059) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0114 : (nb064_alpha_dummy_059) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_059, fv_syn_c1c] using (nb064_compact_fv_empty_0040)

theorem nb064_compact_fv_empty_0041 (y : Var) (z : Var) : (nb064_alpha_dummy_060 y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0115 (y : Var) (z : Var) : (nb064_alpha_dummy_060 y z) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_060, fv_syn_c1c] using (nb064_compact_fv_empty_0041 y z)

theorem nb064_compact_fv_empty_0042 : (nb064_alpha_dummy_055) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0116 : (nb064_alpha_dummy_055) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_055, fv_syn_c1c] using (nb064_compact_fv_empty_0042)

theorem nb064_compact_fv_empty_0043 (y : Var) (z : Var) : (nb064_alpha_dummy_057 y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0117 (y : Var) (z : Var) : (nb064_alpha_dummy_057 y z) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_057, fv_syn_c1c] using (nb064_compact_fv_empty_0043 y z)

theorem nb064_compact_fv_empty_0044 : (nb064_alpha_dummy_056) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0118 : (nb064_alpha_dummy_056) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_056, fv_syn_c1c] using (nb064_compact_fv_empty_0044)

theorem nb064_compact_fv_empty_0045 (y : Var) (z : Var) : (nb064_alpha_dummy_058 y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0119 (y : Var) (z : Var) : (nb064_alpha_dummy_058 y z) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_058, fv_syn_c1c] using (nb064_compact_fv_empty_0045 y z)

theorem nb064_compact_fv_empty_0046 : (nb064_alpha_dummy_048) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0120 : (nb064_alpha_dummy_048) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_048, fv_syn_c1c] using (nb064_compact_fv_empty_0046)

theorem nb064_compact_fv_empty_0047 (y : Var) (z : Var) : (nb064_alpha_dummy_050 y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0121 (y : Var) (z : Var) : (nb064_alpha_dummy_050 y z) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_050, fv_syn_c1c] using (nb064_compact_fv_empty_0047 y z)

theorem nb064_compact_fv_empty_0048 : (nb064_alpha_dummy_047) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0122 : (nb064_alpha_dummy_047) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_047, fv_syn_c1c] using (nb064_compact_fv_empty_0048)

theorem nb064_compact_fv_empty_0049 (y : Var) (z : Var) : (nb064_alpha_dummy_049 y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0123 (y : Var) (z : Var) : (nb064_alpha_dummy_049 y z) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_049, fv_syn_c1c] using (nb064_compact_fv_empty_0049 y z)

theorem nb064_compact_fv_empty_0050 : (nb064_alpha_dummy_053) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0124 : (nb064_alpha_dummy_053) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_053, fv_syn_c1c] using (nb064_compact_fv_empty_0050)

theorem nb064_compact_fv_empty_0051 (y : Var) (z : Var) : (nb064_alpha_dummy_054 y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0125 (y : Var) (z : Var) : (nb064_alpha_dummy_054 y z) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_054, fv_syn_c1c] using (nb064_compact_fv_empty_0051 y z)

theorem nb064_compact_fv_empty_0052 : (nb064_alpha_dummy_051) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0126 : (nb064_alpha_dummy_051) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_051, fv_syn_c1c] using (nb064_compact_fv_empty_0052)

theorem nb064_compact_fv_empty_0053 (y : Var) (z : Var) : (nb064_alpha_dummy_052 y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0127 (y : Var) (z : Var) : (nb064_alpha_dummy_052 y z) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_052, fv_syn_c1c] using (nb064_compact_fv_empty_0053 y z)

theorem nb064_compact_fv_empty_0054 : (nb064_alpha_dummy_003) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0128 : (nb064_alpha_dummy_003) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_003, fv_syn_c1c] using (nb064_compact_fv_empty_0054)

theorem nb064_compact_fv_empty_0055 (y : Var) : y ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0129 (y : Var) : y ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb064_compact_fv_empty_0055 y)

theorem nb064_compact_fv_empty_0056 : (nb064_alpha_dummy_004) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0130 : (nb064_alpha_dummy_004) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_004, fv_syn_c1c] using (nb064_compact_fv_empty_0056)

theorem nb064_compact_fv_empty_0057 (z : Var) : z ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb064_wpp_notmem_0131 (z : Var) : z ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb064_compact_fv_empty_0057 z)

theorem nb064_wpp_notmem_0132 : (nb064_alpha_dummy_002) ∉ ((syn_c1c)).fv := by
  simpa only [nb064_alpha_dummy_002, fv_syn_c1c] using (nb064_compact_fv_empty_0032)

theorem nb064_wpp_notmem_0133 (x : Var) : x ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb064_compact_fv_empty_0033 x)

theorem nb064_compact_envfresh_0008 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb064_alpha_dummy_063), (nb064_alpha_dummy_066 y z)), ((nb064_alpha_dummy_062), (nb064_alpha_dummy_065 y z)), ((nb064_alpha_dummy_061), (nb064_alpha_dummy_064 y z)), ((nb064_alpha_dummy_059), (nb064_alpha_dummy_060 y z)), ((nb064_alpha_dummy_055), (nb064_alpha_dummy_057 y z)), ((nb064_alpha_dummy_056), (nb064_alpha_dummy_058 y z)), ((nb064_alpha_dummy_048), (nb064_alpha_dummy_050 y z)), ((nb064_alpha_dummy_047), (nb064_alpha_dummy_049 y z)), ((nb064_alpha_dummy_053), (nb064_alpha_dummy_054 y z)), ((nb064_alpha_dummy_051), (nb064_alpha_dummy_052 y z)), ((nb064_alpha_dummy_003), y), ((nb064_alpha_dummy_004), z), ((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb064_alpha_dummy_063) (nb064_alpha_dummy_066 y z) (nb064_wpp_notmem_0108) (nb064_wpp_notmem_0109 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_062) (nb064_alpha_dummy_065 y z) (nb064_wpp_notmem_0110) (nb064_wpp_notmem_0111 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_061) (nb064_alpha_dummy_064 y z) (nb064_wpp_notmem_0112) (nb064_wpp_notmem_0113 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_059) (nb064_alpha_dummy_060 y z) (nb064_wpp_notmem_0114) (nb064_wpp_notmem_0115 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_055) (nb064_alpha_dummy_057 y z) (nb064_wpp_notmem_0116) (nb064_wpp_notmem_0117 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_056) (nb064_alpha_dummy_058 y z) (nb064_wpp_notmem_0118) (nb064_wpp_notmem_0119 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_048) (nb064_alpha_dummy_050 y z) (nb064_wpp_notmem_0120) (nb064_wpp_notmem_0121 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_047) (nb064_alpha_dummy_049 y z) (nb064_wpp_notmem_0122) (nb064_wpp_notmem_0123 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_053) (nb064_alpha_dummy_054 y z) (nb064_wpp_notmem_0124) (nb064_wpp_notmem_0125 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_051) (nb064_alpha_dummy_052 y z) (nb064_wpp_notmem_0126) (nb064_wpp_notmem_0127 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_003) y (nb064_wpp_notmem_0128) (nb064_wpp_notmem_0129 y) (TEnvFresh.consFresh (nb064_alpha_dummy_004) z (nb064_wpp_notmem_0130) (nb064_wpp_notmem_0131 z) (TEnvFresh.consFresh (nb064_alpha_dummy_002) x (nb064_wpp_notmem_0132) (nb064_wpp_notmem_0133 x) (TEnvFresh.consFresh (nb064_alpha_dummy_000) a (nb064_wpp_notmem_0020) (nb064_wpp_notmem_0021 a) (TEnvFresh.consFresh (nb064_alpha_dummy_001) r (nb064_wpp_notmem_0022) (nb064_wpp_notmem_0023 r) (TEnvFresh.consFresh (nb064_alpha_dummy_005) (nb064_alpha_dummy_006 x y z r a) (nb064_wpp_notmem_0024) (nb064_wpp_notmem_0025 x y z r a) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))

noncomputable def nb064_wpp_refl_0008 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb064_alpha_dummy_063), (nb064_alpha_dummy_066 y z)), ((nb064_alpha_dummy_062), (nb064_alpha_dummy_065 y z)), ((nb064_alpha_dummy_061), (nb064_alpha_dummy_064 y z)), ((nb064_alpha_dummy_059), (nb064_alpha_dummy_060 y z)), ((nb064_alpha_dummy_055), (nb064_alpha_dummy_057 y z)), ((nb064_alpha_dummy_056), (nb064_alpha_dummy_058 y z)), ((nb064_alpha_dummy_048), (nb064_alpha_dummy_050 y z)), ((nb064_alpha_dummy_047), (nb064_alpha_dummy_049 y z)), ((nb064_alpha_dummy_053), (nb064_alpha_dummy_054 y z)), ((nb064_alpha_dummy_051), (nb064_alpha_dummy_052 y z)), ((nb064_alpha_dummy_003), y), ((nb064_alpha_dummy_004), z), ((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb064_compact_envfresh_0008 x y z r a)

theorem nb064_wpp_notmem_0134 : (nb064_alpha_dummy_063) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_063, fv_syn_c0] using (nb064_compact_fv_empty_0034)

theorem nb064_wpp_notmem_0135 (y : Var) (z : Var) : (nb064_alpha_dummy_066 y z) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_066, fv_syn_c0] using (nb064_compact_fv_empty_0035 y z)

theorem nb064_wpp_notmem_0136 : (nb064_alpha_dummy_062) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_062, fv_syn_c0] using (nb064_compact_fv_empty_0036)

theorem nb064_wpp_notmem_0137 (y : Var) (z : Var) : (nb064_alpha_dummy_065 y z) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_065, fv_syn_c0] using (nb064_compact_fv_empty_0037 y z)

theorem nb064_wpp_notmem_0138 : (nb064_alpha_dummy_061) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_061, fv_syn_c0] using (nb064_compact_fv_empty_0038)

theorem nb064_wpp_notmem_0139 (y : Var) (z : Var) : (nb064_alpha_dummy_064 y z) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_064, fv_syn_c0] using (nb064_compact_fv_empty_0039 y z)

theorem nb064_wpp_notmem_0140 : (nb064_alpha_dummy_059) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_059, fv_syn_c0] using (nb064_compact_fv_empty_0040)

theorem nb064_wpp_notmem_0141 (y : Var) (z : Var) : (nb064_alpha_dummy_060 y z) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_060, fv_syn_c0] using (nb064_compact_fv_empty_0041 y z)

theorem nb064_wpp_notmem_0142 : (nb064_alpha_dummy_055) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_055, fv_syn_c0] using (nb064_compact_fv_empty_0042)

theorem nb064_wpp_notmem_0143 (y : Var) (z : Var) : (nb064_alpha_dummy_057 y z) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_057, fv_syn_c0] using (nb064_compact_fv_empty_0043 y z)

theorem nb064_wpp_notmem_0144 : (nb064_alpha_dummy_056) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_056, fv_syn_c0] using (nb064_compact_fv_empty_0044)

theorem nb064_wpp_notmem_0145 (y : Var) (z : Var) : (nb064_alpha_dummy_058 y z) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_058, fv_syn_c0] using (nb064_compact_fv_empty_0045 y z)

theorem nb064_wpp_notmem_0146 : (nb064_alpha_dummy_048) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_048, fv_syn_c0] using (nb064_compact_fv_empty_0046)

theorem nb064_wpp_notmem_0147 (y : Var) (z : Var) : (nb064_alpha_dummy_050 y z) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_050, fv_syn_c0] using (nb064_compact_fv_empty_0047 y z)

theorem nb064_wpp_notmem_0148 : (nb064_alpha_dummy_047) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_047, fv_syn_c0] using (nb064_compact_fv_empty_0048)

theorem nb064_wpp_notmem_0149 (y : Var) (z : Var) : (nb064_alpha_dummy_049 y z) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_049, fv_syn_c0] using (nb064_compact_fv_empty_0049 y z)

theorem nb064_wpp_notmem_0150 : (nb064_alpha_dummy_053) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_053, fv_syn_c0] using (nb064_compact_fv_empty_0050)

theorem nb064_wpp_notmem_0151 (y : Var) (z : Var) : (nb064_alpha_dummy_054 y z) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_054, fv_syn_c0] using (nb064_compact_fv_empty_0051 y z)

theorem nb064_wpp_notmem_0152 : (nb064_alpha_dummy_051) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_051, fv_syn_c0] using (nb064_compact_fv_empty_0052)

theorem nb064_wpp_notmem_0153 (y : Var) (z : Var) : (nb064_alpha_dummy_052 y z) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_052, fv_syn_c0] using (nb064_compact_fv_empty_0053 y z)

theorem nb064_wpp_notmem_0154 : (nb064_alpha_dummy_003) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_003, fv_syn_c0] using (nb064_compact_fv_empty_0054)

theorem nb064_wpp_notmem_0155 (y : Var) : y ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb064_compact_fv_empty_0055 y)

theorem nb064_wpp_notmem_0156 : (nb064_alpha_dummy_004) ∉ ((syn_c0)).fv := by
  simpa only [nb064_alpha_dummy_004, fv_syn_c0] using (nb064_compact_fv_empty_0056)

theorem nb064_wpp_notmem_0157 (z : Var) : z ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb064_compact_fv_empty_0057 z)

theorem nb064_compact_envfresh_0009 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb064_alpha_dummy_063), (nb064_alpha_dummy_066 y z)), ((nb064_alpha_dummy_062), (nb064_alpha_dummy_065 y z)), ((nb064_alpha_dummy_061), (nb064_alpha_dummy_064 y z)), ((nb064_alpha_dummy_059), (nb064_alpha_dummy_060 y z)), ((nb064_alpha_dummy_055), (nb064_alpha_dummy_057 y z)), ((nb064_alpha_dummy_056), (nb064_alpha_dummy_058 y z)), ((nb064_alpha_dummy_048), (nb064_alpha_dummy_050 y z)), ((nb064_alpha_dummy_047), (nb064_alpha_dummy_049 y z)), ((nb064_alpha_dummy_053), (nb064_alpha_dummy_054 y z)), ((nb064_alpha_dummy_051), (nb064_alpha_dummy_052 y z)), ((nb064_alpha_dummy_003), y), ((nb064_alpha_dummy_004), z), ((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb064_alpha_dummy_063) (nb064_alpha_dummy_066 y z) (nb064_wpp_notmem_0134) (nb064_wpp_notmem_0135 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_062) (nb064_alpha_dummy_065 y z) (nb064_wpp_notmem_0136) (nb064_wpp_notmem_0137 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_061) (nb064_alpha_dummy_064 y z) (nb064_wpp_notmem_0138) (nb064_wpp_notmem_0139 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_059) (nb064_alpha_dummy_060 y z) (nb064_wpp_notmem_0140) (nb064_wpp_notmem_0141 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_055) (nb064_alpha_dummy_057 y z) (nb064_wpp_notmem_0142) (nb064_wpp_notmem_0143 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_056) (nb064_alpha_dummy_058 y z) (nb064_wpp_notmem_0144) (nb064_wpp_notmem_0145 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_048) (nb064_alpha_dummy_050 y z) (nb064_wpp_notmem_0146) (nb064_wpp_notmem_0147 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_047) (nb064_alpha_dummy_049 y z) (nb064_wpp_notmem_0148) (nb064_wpp_notmem_0149 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_053) (nb064_alpha_dummy_054 y z) (nb064_wpp_notmem_0150) (nb064_wpp_notmem_0151 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_051) (nb064_alpha_dummy_052 y z) (nb064_wpp_notmem_0152) (nb064_wpp_notmem_0153 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_003) y (nb064_wpp_notmem_0154) (nb064_wpp_notmem_0155 y) (TEnvFresh.consFresh (nb064_alpha_dummy_004) z (nb064_wpp_notmem_0156) (nb064_wpp_notmem_0157 z) (TEnvFresh.consFresh (nb064_alpha_dummy_002) x (nb064_wpp_notmem_0106) (nb064_wpp_notmem_0107 x) (TEnvFresh.consFresh (nb064_alpha_dummy_000) a (nb064_wpp_notmem_0046) (nb064_wpp_notmem_0047 a) (TEnvFresh.consFresh (nb064_alpha_dummy_001) r (nb064_wpp_notmem_0048) (nb064_wpp_notmem_0049 r) (TEnvFresh.consFresh (nb064_alpha_dummy_005) (nb064_alpha_dummy_006 x y z r a) (nb064_wpp_notmem_0050) (nb064_wpp_notmem_0051 x y z r a) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))

noncomputable def nb064_wpp_refl_0009 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb064_alpha_dummy_063), (nb064_alpha_dummy_066 y z)), ((nb064_alpha_dummy_062), (nb064_alpha_dummy_065 y z)), ((nb064_alpha_dummy_061), (nb064_alpha_dummy_064 y z)), ((nb064_alpha_dummy_059), (nb064_alpha_dummy_060 y z)), ((nb064_alpha_dummy_055), (nb064_alpha_dummy_057 y z)), ((nb064_alpha_dummy_056), (nb064_alpha_dummy_058 y z)), ((nb064_alpha_dummy_048), (nb064_alpha_dummy_050 y z)), ((nb064_alpha_dummy_047), (nb064_alpha_dummy_049 y z)), ((nb064_alpha_dummy_053), (nb064_alpha_dummy_054 y z)), ((nb064_alpha_dummy_051), (nb064_alpha_dummy_052 y z)), ((nb064_alpha_dummy_003), y), ((nb064_alpha_dummy_004), z), ((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb064_compact_envfresh_0009 x y z r a)

noncomputable def nb064_split_alpha_0005 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TAlphaWff [((nb064_alpha_dummy_063), (nb064_alpha_dummy_066 y z)), ((nb064_alpha_dummy_062), (nb064_alpha_dummy_065 y z)), ((nb064_alpha_dummy_061), (nb064_alpha_dummy_064 y z)), ((nb064_alpha_dummy_059), (nb064_alpha_dummy_060 y z)), ((nb064_alpha_dummy_055), (nb064_alpha_dummy_057 y z)), ((nb064_alpha_dummy_056), (nb064_alpha_dummy_058 y z)), ((nb064_alpha_dummy_048), (nb064_alpha_dummy_050 y z)), ((nb064_alpha_dummy_047), (nb064_alpha_dummy_049 y z)), ((nb064_alpha_dummy_053), (nb064_alpha_dummy_054 y z)), ((nb064_alpha_dummy_051), (nb064_alpha_dummy_052 y z)), ((nb064_alpha_dummy_003), y), ((nb064_alpha_dummy_004), z), ((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb064_alpha_dummy_062)) (Class.cv (nb064_alpha_dummy_063))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb064_alpha_dummy_061)) (syn_cun (Class.cv (nb064_alpha_dummy_062)) (Class.cv (nb064_alpha_dummy_063)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb064_alpha_dummy_065 y z)) (Class.cv (nb064_alpha_dummy_066 y z))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb064_alpha_dummy_064 y z)) (syn_cun (Class.cv (nb064_alpha_dummy_065 y z)) (Class.cv (nb064_alpha_dummy_066 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0065 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0063 y z) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0069 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0067 y z) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0065 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0063 y z) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0069 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0067 y z) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb064_alpha_dummy_063), (nb064_alpha_dummy_066 y z)), ((nb064_alpha_dummy_062), (nb064_alpha_dummy_065 y z)), ((nb064_alpha_dummy_061), (nb064_alpha_dummy_064 y z)), ((nb064_alpha_dummy_059), (nb064_alpha_dummy_060 y z)), ((nb064_alpha_dummy_055), (nb064_alpha_dummy_057 y z)), ((nb064_alpha_dummy_056), (nb064_alpha_dummy_058 y z)), ((nb064_alpha_dummy_048), (nb064_alpha_dummy_050 y z)), ((nb064_alpha_dummy_047), (nb064_alpha_dummy_049 y z)), ((nb064_alpha_dummy_053), (nb064_alpha_dummy_054 y z)), ((nb064_alpha_dummy_051), (nb064_alpha_dummy_052 y z)), ((nb064_alpha_dummy_003), y), ((nb064_alpha_dummy_004), z), ((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] (syn_c0) (nb064_wpp_refl_0009 x y z r a))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0073 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0071 y z) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0073 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0071 y z) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0076) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0077 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0075 y z) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0076) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0077 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0075 y z) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb064_wpp_notmem_0158 : (nb064_alpha_dummy_059) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_059, fv_syn_cnnc] using (nb064_compact_fv_empty_0040)

theorem nb064_wpp_notmem_0159 (y : Var) (z : Var) : (nb064_alpha_dummy_060 y z) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_060, fv_syn_cnnc] using (nb064_compact_fv_empty_0041 y z)

theorem nb064_wpp_notmem_0160 : (nb064_alpha_dummy_055) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_055, fv_syn_cnnc] using (nb064_compact_fv_empty_0042)

theorem nb064_wpp_notmem_0161 (y : Var) (z : Var) : (nb064_alpha_dummy_057 y z) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_057, fv_syn_cnnc] using (nb064_compact_fv_empty_0043 y z)

theorem nb064_wpp_notmem_0162 : (nb064_alpha_dummy_056) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_056, fv_syn_cnnc] using (nb064_compact_fv_empty_0044)

theorem nb064_wpp_notmem_0163 (y : Var) (z : Var) : (nb064_alpha_dummy_058 y z) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_058, fv_syn_cnnc] using (nb064_compact_fv_empty_0045 y z)

theorem nb064_wpp_notmem_0164 : (nb064_alpha_dummy_048) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_048, fv_syn_cnnc] using (nb064_compact_fv_empty_0046)

theorem nb064_wpp_notmem_0165 (y : Var) (z : Var) : (nb064_alpha_dummy_050 y z) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_050, fv_syn_cnnc] using (nb064_compact_fv_empty_0047 y z)

theorem nb064_wpp_notmem_0166 : (nb064_alpha_dummy_047) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_047, fv_syn_cnnc] using (nb064_compact_fv_empty_0048)

theorem nb064_wpp_notmem_0167 (y : Var) (z : Var) : (nb064_alpha_dummy_049 y z) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_049, fv_syn_cnnc] using (nb064_compact_fv_empty_0049 y z)

theorem nb064_wpp_notmem_0168 : (nb064_alpha_dummy_053) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_053, fv_syn_cnnc] using (nb064_compact_fv_empty_0050)

theorem nb064_wpp_notmem_0169 (y : Var) (z : Var) : (nb064_alpha_dummy_054 y z) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_054, fv_syn_cnnc] using (nb064_compact_fv_empty_0051 y z)

theorem nb064_wpp_notmem_0170 : (nb064_alpha_dummy_051) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_051, fv_syn_cnnc] using (nb064_compact_fv_empty_0052)

theorem nb064_wpp_notmem_0171 (y : Var) (z : Var) : (nb064_alpha_dummy_052 y z) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_052, fv_syn_cnnc] using (nb064_compact_fv_empty_0053 y z)

theorem nb064_wpp_notmem_0172 : (nb064_alpha_dummy_003) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_003, fv_syn_cnnc] using (nb064_compact_fv_empty_0054)

theorem nb064_wpp_notmem_0173 (y : Var) : y ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb064_compact_fv_empty_0055 y)

theorem nb064_wpp_notmem_0174 : (nb064_alpha_dummy_004) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_004, fv_syn_cnnc] using (nb064_compact_fv_empty_0056)

theorem nb064_wpp_notmem_0175 (z : Var) : z ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb064_compact_fv_empty_0057 z)

theorem nb064_wpp_notmem_0176 : (nb064_alpha_dummy_002) ∉ ((syn_cnnc)).fv := by
  simpa only [nb064_alpha_dummy_002, fv_syn_cnnc] using (nb064_compact_fv_empty_0032)

theorem nb064_wpp_notmem_0177 (x : Var) : x ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb064_compact_fv_empty_0033 x)

theorem nb064_compact_envfresh_0010 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb064_alpha_dummy_059), (nb064_alpha_dummy_060 y z)), ((nb064_alpha_dummy_055), (nb064_alpha_dummy_057 y z)), ((nb064_alpha_dummy_056), (nb064_alpha_dummy_058 y z)), ((nb064_alpha_dummy_048), (nb064_alpha_dummy_050 y z)), ((nb064_alpha_dummy_047), (nb064_alpha_dummy_049 y z)), ((nb064_alpha_dummy_053), (nb064_alpha_dummy_054 y z)), ((nb064_alpha_dummy_051), (nb064_alpha_dummy_052 y z)), ((nb064_alpha_dummy_003), y), ((nb064_alpha_dummy_004), z), ((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb064_alpha_dummy_059) (nb064_alpha_dummy_060 y z) (nb064_wpp_notmem_0158) (nb064_wpp_notmem_0159 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_055) (nb064_alpha_dummy_057 y z) (nb064_wpp_notmem_0160) (nb064_wpp_notmem_0161 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_056) (nb064_alpha_dummy_058 y z) (nb064_wpp_notmem_0162) (nb064_wpp_notmem_0163 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_048) (nb064_alpha_dummy_050 y z) (nb064_wpp_notmem_0164) (nb064_wpp_notmem_0165 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_047) (nb064_alpha_dummy_049 y z) (nb064_wpp_notmem_0166) (nb064_wpp_notmem_0167 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_053) (nb064_alpha_dummy_054 y z) (nb064_wpp_notmem_0168) (nb064_wpp_notmem_0169 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_051) (nb064_alpha_dummy_052 y z) (nb064_wpp_notmem_0170) (nb064_wpp_notmem_0171 y z) (TEnvFresh.consFresh (nb064_alpha_dummy_003) y (nb064_wpp_notmem_0172) (nb064_wpp_notmem_0173 y) (TEnvFresh.consFresh (nb064_alpha_dummy_004) z (nb064_wpp_notmem_0174) (nb064_wpp_notmem_0175 z) (TEnvFresh.consFresh (nb064_alpha_dummy_002) x (nb064_wpp_notmem_0176) (nb064_wpp_notmem_0177 x) (TEnvFresh.consFresh (nb064_alpha_dummy_000) a (nb064_wpp_notmem_0066) (nb064_wpp_notmem_0067 a) (TEnvFresh.consFresh (nb064_alpha_dummy_001) r (nb064_wpp_notmem_0068) (nb064_wpp_notmem_0069 r) (TEnvFresh.consFresh (nb064_alpha_dummy_005) (nb064_alpha_dummy_006 x y z r a) (nb064_wpp_notmem_0070) (nb064_wpp_notmem_0071 x y z r a) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))

noncomputable def nb064_wpp_refl_0010 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb064_alpha_dummy_059), (nb064_alpha_dummy_060 y z)), ((nb064_alpha_dummy_055), (nb064_alpha_dummy_057 y z)), ((nb064_alpha_dummy_056), (nb064_alpha_dummy_058 y z)), ((nb064_alpha_dummy_048), (nb064_alpha_dummy_050 y z)), ((nb064_alpha_dummy_047), (nb064_alpha_dummy_049 y z)), ((nb064_alpha_dummy_053), (nb064_alpha_dummy_054 y z)), ((nb064_alpha_dummy_051), (nb064_alpha_dummy_052 y z)), ((nb064_alpha_dummy_003), y), ((nb064_alpha_dummy_004), z), ((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb064_compact_envfresh_0010 x y z r a)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
