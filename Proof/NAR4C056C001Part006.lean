import NAR4C056C001Part005

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

theorem nb056_wpp_notmem_0034 : (nb056_alpha_dummy_028) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_028, fv_syn_c0] using (nb056_compact_fv_empty_0002)

theorem nb056_wpp_notmem_0035 (f : Var) : (nb056_alpha_dummy_031 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_031, fv_syn_c0] using (nb056_compact_fv_empty_0003 f)

theorem nb056_wpp_notmem_0036 : (nb056_alpha_dummy_027) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_027, fv_syn_c0] using (nb056_compact_fv_empty_0004)

theorem nb056_wpp_notmem_0037 (f : Var) : (nb056_alpha_dummy_030 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_030, fv_syn_c0] using (nb056_compact_fv_empty_0005 f)

theorem nb056_wpp_notmem_0038 : (nb056_alpha_dummy_025) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_025, fv_syn_c0] using (nb056_compact_fv_empty_0006)

theorem nb056_wpp_notmem_0039 (f : Var) : (nb056_alpha_dummy_026 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_026, fv_syn_c0] using (nb056_compact_fv_empty_0007 f)

theorem nb056_wpp_notmem_0040 : (nb056_alpha_dummy_021) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_021, fv_syn_c0] using (nb056_compact_fv_empty_0008)

theorem nb056_wpp_notmem_0041 (f : Var) : (nb056_alpha_dummy_023 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_023, fv_syn_c0] using (nb056_compact_fv_empty_0009 f)

theorem nb056_wpp_notmem_0042 : (nb056_alpha_dummy_022) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_022, fv_syn_c0] using (nb056_compact_fv_empty_0010)

theorem nb056_wpp_notmem_0043 (f : Var) : (nb056_alpha_dummy_024 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_024, fv_syn_c0] using (nb056_compact_fv_empty_0011 f)

theorem nb056_wpp_notmem_0044 : (nb056_alpha_dummy_014) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_014, fv_syn_c0] using (nb056_compact_fv_empty_0012)

theorem nb056_wpp_notmem_0045 (f : Var) : (nb056_alpha_dummy_016 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_016, fv_syn_c0] using (nb056_compact_fv_empty_0013 f)

theorem nb056_wpp_notmem_0046 : (nb056_alpha_dummy_013) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_013, fv_syn_c0] using (nb056_compact_fv_empty_0014)

theorem nb056_wpp_notmem_0047 (f : Var) : (nb056_alpha_dummy_015 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_015, fv_syn_c0] using (nb056_compact_fv_empty_0015 f)

theorem nb056_wpp_notmem_0048 : (nb056_alpha_dummy_019) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_019, fv_syn_c0] using (nb056_compact_fv_empty_0016)

theorem nb056_wpp_notmem_0049 (f : Var) : (nb056_alpha_dummy_020 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_020, fv_syn_c0] using (nb056_compact_fv_empty_0017 f)

theorem nb056_wpp_notmem_0050 : (nb056_alpha_dummy_017) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_017, fv_syn_c0] using (nb056_compact_fv_empty_0018)

theorem nb056_wpp_notmem_0051 (f : Var) : (nb056_alpha_dummy_018 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_018, fv_syn_c0] using (nb056_compact_fv_empty_0019 f)

theorem nb056_wpp_notmem_0052 : (nb056_alpha_dummy_006) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_006, fv_syn_c0] using (nb056_compact_fv_empty_0020)

theorem nb056_wpp_notmem_0053 (f : Var) : (nb056_alpha_dummy_009 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_009, fv_syn_c0] using (nb056_compact_fv_empty_0021 f)

theorem nb056_wpp_notmem_0054 : (nb056_alpha_dummy_005) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_005, fv_syn_c0] using (nb056_compact_fv_empty_0022)

theorem nb056_wpp_notmem_0055 (f : Var) : (nb056_alpha_dummy_008 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_008, fv_syn_c0] using (nb056_compact_fv_empty_0023 f)

theorem nb056_wpp_notmem_0056 : (nb056_alpha_dummy_011) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_011, fv_syn_c0] using (nb056_compact_fv_empty_0024)

theorem nb056_wpp_notmem_0057 (f : Var) : (nb056_alpha_dummy_012 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_012, fv_syn_c0] using (nb056_compact_fv_empty_0025 f)

theorem nb056_wpp_notmem_0058 : (nb056_alpha_dummy_003) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_003, fv_syn_c0] using (nb056_compact_fv_empty_0026)

theorem nb056_wpp_notmem_0059 (f : Var) : (nb056_alpha_dummy_004 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_004, fv_syn_c0] using (nb056_compact_fv_empty_0027 f)

theorem nb056_wpp_notmem_0060 : (nb056_alpha_dummy_001) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_001, fv_syn_c0] using (nb056_compact_fv_empty_0028)

theorem nb056_wpp_notmem_0061 (f : Var) : (nb056_alpha_dummy_002 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_002, fv_syn_c0] using (nb056_compact_fv_empty_0029 f)

theorem nb056_wpp_notmem_0062 : (nb056_alpha_dummy_000) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_000, fv_syn_c0] using (nb056_compact_fv_empty_0030)

theorem nb056_wpp_notmem_0063 (f : Var) : f ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb056_compact_fv_empty_0031 f)

theorem nb056_compact_envfresh_0001 (f : Var) : TEnvFresh [((nb056_alpha_dummy_029), (nb056_alpha_dummy_032 f)), ((nb056_alpha_dummy_028), (nb056_alpha_dummy_031 f)), ((nb056_alpha_dummy_027), (nb056_alpha_dummy_030 f)), ((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)), ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)), ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_019), (nb056_alpha_dummy_020 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb056_alpha_dummy_029) (nb056_alpha_dummy_032 f) (nb056_wpp_notmem_0032) (nb056_wpp_notmem_0033 f) (TEnvFresh.consFresh (nb056_alpha_dummy_028) (nb056_alpha_dummy_031 f) (nb056_wpp_notmem_0034) (nb056_wpp_notmem_0035 f) (TEnvFresh.consFresh (nb056_alpha_dummy_027) (nb056_alpha_dummy_030 f) (nb056_wpp_notmem_0036) (nb056_wpp_notmem_0037 f) (TEnvFresh.consFresh (nb056_alpha_dummy_025) (nb056_alpha_dummy_026 f) (nb056_wpp_notmem_0038) (nb056_wpp_notmem_0039 f) (TEnvFresh.consFresh (nb056_alpha_dummy_021) (nb056_alpha_dummy_023 f) (nb056_wpp_notmem_0040) (nb056_wpp_notmem_0041 f) (TEnvFresh.consFresh (nb056_alpha_dummy_022) (nb056_alpha_dummy_024 f) (nb056_wpp_notmem_0042) (nb056_wpp_notmem_0043 f) (TEnvFresh.consFresh (nb056_alpha_dummy_014) (nb056_alpha_dummy_016 f) (nb056_wpp_notmem_0044) (nb056_wpp_notmem_0045 f) (TEnvFresh.consFresh (nb056_alpha_dummy_013) (nb056_alpha_dummy_015 f) (nb056_wpp_notmem_0046) (nb056_wpp_notmem_0047 f) (TEnvFresh.consFresh (nb056_alpha_dummy_019) (nb056_alpha_dummy_020 f) (nb056_wpp_notmem_0048) (nb056_wpp_notmem_0049 f) (TEnvFresh.consFresh (nb056_alpha_dummy_017) (nb056_alpha_dummy_018 f) (nb056_wpp_notmem_0050) (nb056_wpp_notmem_0051 f) (TEnvFresh.consFresh (nb056_alpha_dummy_006) (nb056_alpha_dummy_009 f) (nb056_wpp_notmem_0052) (nb056_wpp_notmem_0053 f) (TEnvFresh.consFresh (nb056_alpha_dummy_005) (nb056_alpha_dummy_008 f) (nb056_wpp_notmem_0054) (nb056_wpp_notmem_0055 f) (TEnvFresh.consFresh (nb056_alpha_dummy_011) (nb056_alpha_dummy_012 f) (nb056_wpp_notmem_0056) (nb056_wpp_notmem_0057 f) (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f) (nb056_wpp_notmem_0058) (nb056_wpp_notmem_0059 f) (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f) (nb056_wpp_notmem_0060) (nb056_wpp_notmem_0061 f) (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0062) (nb056_wpp_notmem_0063 f) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))

noncomputable def nb056_wpp_refl_0001 (f : Var) : TReflOn [((nb056_alpha_dummy_029), (nb056_alpha_dummy_032 f)), ((nb056_alpha_dummy_028), (nb056_alpha_dummy_031 f)), ((nb056_alpha_dummy_027), (nb056_alpha_dummy_030 f)), ((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)), ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)), ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_019), (nb056_alpha_dummy_020 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0001 f)

noncomputable def nb056_split_alpha_0000 (f : Var) : TAlphaWff [((nb056_alpha_dummy_029), (nb056_alpha_dummy_032 f)), ((nb056_alpha_dummy_028), (nb056_alpha_dummy_031 f)), ((nb056_alpha_dummy_027), (nb056_alpha_dummy_030 f)), ((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)), ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)), ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_019), (nb056_alpha_dummy_020 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb056_alpha_dummy_028)) (Class.cv (nb056_alpha_dummy_029))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_027)) (syn_cun (Class.cv (nb056_alpha_dummy_028)) (Class.cv (nb056_alpha_dummy_029)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb056_alpha_dummy_031 f)) (Class.cv (nb056_alpha_dummy_032 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_030 f)) (syn_cun (Class.cv (nb056_alpha_dummy_031 f)) (Class.cv (nb056_alpha_dummy_032 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0019 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0017 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0023 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0021 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0019 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0017 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0023 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0021 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_029), (nb056_alpha_dummy_032 f)), ((nb056_alpha_dummy_028), (nb056_alpha_dummy_031 f)), ((nb056_alpha_dummy_027), (nb056_alpha_dummy_030 f)), ((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)), ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)), ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_019), (nb056_alpha_dummy_020 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_c0) (nb056_wpp_refl_0001 f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0027 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0025 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0027 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0025 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0031 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0029 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0031 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0029 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb056_wpp_notmem_0064 : (nb056_alpha_dummy_025) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_025, fv_syn_cnnc] using (nb056_compact_fv_empty_0006)

theorem nb056_wpp_notmem_0065 (f : Var) : (nb056_alpha_dummy_026 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_026, fv_syn_cnnc] using (nb056_compact_fv_empty_0007 f)

theorem nb056_wpp_notmem_0066 : (nb056_alpha_dummy_021) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_021, fv_syn_cnnc] using (nb056_compact_fv_empty_0008)

theorem nb056_wpp_notmem_0067 (f : Var) : (nb056_alpha_dummy_023 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_023, fv_syn_cnnc] using (nb056_compact_fv_empty_0009 f)

theorem nb056_wpp_notmem_0068 : (nb056_alpha_dummy_022) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_022, fv_syn_cnnc] using (nb056_compact_fv_empty_0010)

theorem nb056_wpp_notmem_0069 (f : Var) : (nb056_alpha_dummy_024 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_024, fv_syn_cnnc] using (nb056_compact_fv_empty_0011 f)

theorem nb056_wpp_notmem_0070 : (nb056_alpha_dummy_014) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_014, fv_syn_cnnc] using (nb056_compact_fv_empty_0012)

theorem nb056_wpp_notmem_0071 (f : Var) : (nb056_alpha_dummy_016 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_016, fv_syn_cnnc] using (nb056_compact_fv_empty_0013 f)

theorem nb056_wpp_notmem_0072 : (nb056_alpha_dummy_013) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_013, fv_syn_cnnc] using (nb056_compact_fv_empty_0014)

theorem nb056_wpp_notmem_0073 (f : Var) : (nb056_alpha_dummy_015 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_015, fv_syn_cnnc] using (nb056_compact_fv_empty_0015 f)

theorem nb056_wpp_notmem_0074 : (nb056_alpha_dummy_019) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_019, fv_syn_cnnc] using (nb056_compact_fv_empty_0016)

theorem nb056_wpp_notmem_0075 (f : Var) : (nb056_alpha_dummy_020 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_020, fv_syn_cnnc] using (nb056_compact_fv_empty_0017 f)

theorem nb056_wpp_notmem_0076 : (nb056_alpha_dummy_017) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_017, fv_syn_cnnc] using (nb056_compact_fv_empty_0018)

theorem nb056_wpp_notmem_0077 (f : Var) : (nb056_alpha_dummy_018 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_018, fv_syn_cnnc] using (nb056_compact_fv_empty_0019 f)

theorem nb056_wpp_notmem_0078 : (nb056_alpha_dummy_006) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_006, fv_syn_cnnc] using (nb056_compact_fv_empty_0020)

theorem nb056_wpp_notmem_0079 (f : Var) : (nb056_alpha_dummy_009 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_009, fv_syn_cnnc] using (nb056_compact_fv_empty_0021 f)

theorem nb056_wpp_notmem_0080 : (nb056_alpha_dummy_005) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_005, fv_syn_cnnc] using (nb056_compact_fv_empty_0022)

theorem nb056_wpp_notmem_0081 (f : Var) : (nb056_alpha_dummy_008 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_008, fv_syn_cnnc] using (nb056_compact_fv_empty_0023 f)

theorem nb056_wpp_notmem_0082 : (nb056_alpha_dummy_011) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_011, fv_syn_cnnc] using (nb056_compact_fv_empty_0024)

theorem nb056_wpp_notmem_0083 (f : Var) : (nb056_alpha_dummy_012 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_012, fv_syn_cnnc] using (nb056_compact_fv_empty_0025 f)

theorem nb056_wpp_notmem_0084 : (nb056_alpha_dummy_003) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_003, fv_syn_cnnc] using (nb056_compact_fv_empty_0026)

theorem nb056_wpp_notmem_0085 (f : Var) : (nb056_alpha_dummy_004 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_004, fv_syn_cnnc] using (nb056_compact_fv_empty_0027 f)

theorem nb056_wpp_notmem_0086 : (nb056_alpha_dummy_001) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_001, fv_syn_cnnc] using (nb056_compact_fv_empty_0028)

theorem nb056_wpp_notmem_0087 (f : Var) : (nb056_alpha_dummy_002 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_002, fv_syn_cnnc] using (nb056_compact_fv_empty_0029 f)

theorem nb056_wpp_notmem_0088 : (nb056_alpha_dummy_000) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_000, fv_syn_cnnc] using (nb056_compact_fv_empty_0030)

theorem nb056_wpp_notmem_0089 (f : Var) : f ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb056_compact_fv_empty_0031 f)

theorem nb056_compact_envfresh_0002 (f : Var) : TEnvFresh [((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)), ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)), ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_019), (nb056_alpha_dummy_020 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb056_alpha_dummy_025) (nb056_alpha_dummy_026 f) (nb056_wpp_notmem_0064) (nb056_wpp_notmem_0065 f) (TEnvFresh.consFresh (nb056_alpha_dummy_021) (nb056_alpha_dummy_023 f) (nb056_wpp_notmem_0066) (nb056_wpp_notmem_0067 f) (TEnvFresh.consFresh (nb056_alpha_dummy_022) (nb056_alpha_dummy_024 f) (nb056_wpp_notmem_0068) (nb056_wpp_notmem_0069 f) (TEnvFresh.consFresh (nb056_alpha_dummy_014) (nb056_alpha_dummy_016 f) (nb056_wpp_notmem_0070) (nb056_wpp_notmem_0071 f) (TEnvFresh.consFresh (nb056_alpha_dummy_013) (nb056_alpha_dummy_015 f) (nb056_wpp_notmem_0072) (nb056_wpp_notmem_0073 f) (TEnvFresh.consFresh (nb056_alpha_dummy_019) (nb056_alpha_dummy_020 f) (nb056_wpp_notmem_0074) (nb056_wpp_notmem_0075 f) (TEnvFresh.consFresh (nb056_alpha_dummy_017) (nb056_alpha_dummy_018 f) (nb056_wpp_notmem_0076) (nb056_wpp_notmem_0077 f) (TEnvFresh.consFresh (nb056_alpha_dummy_006) (nb056_alpha_dummy_009 f) (nb056_wpp_notmem_0078) (nb056_wpp_notmem_0079 f) (TEnvFresh.consFresh (nb056_alpha_dummy_005) (nb056_alpha_dummy_008 f) (nb056_wpp_notmem_0080) (nb056_wpp_notmem_0081 f) (TEnvFresh.consFresh (nb056_alpha_dummy_011) (nb056_alpha_dummy_012 f) (nb056_wpp_notmem_0082) (nb056_wpp_notmem_0083 f) (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f) (nb056_wpp_notmem_0084) (nb056_wpp_notmem_0085 f) (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f) (nb056_wpp_notmem_0086) (nb056_wpp_notmem_0087 f) (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0088) (nb056_wpp_notmem_0089 f) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))

noncomputable def nb056_wpp_refl_0002 (f : Var) : TReflOn [((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)), ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)), ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_019), (nb056_alpha_dummy_020 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0002 f)

noncomputable def nb056_split_alpha_0001 (f : Var) : TAlphaWff [((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_019), (nb056_alpha_dummy_020 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (Wff.classEq (Class.cv (nb056_alpha_dummy_013)) (syn_cphi (Class.cv (nb056_alpha_dummy_014)))) (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0010) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0011 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0010) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0011 f) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_014))).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_016 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0014) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0015 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0015 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0013 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_029), (nb056_alpha_dummy_032 f)), ((nb056_alpha_dummy_028), (nb056_alpha_dummy_031 f)), ((nb056_alpha_dummy_027), (nb056_alpha_dummy_030 f)), ((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)), ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)), ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_019), (nb056_alpha_dummy_020 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_c1c) (nb056_wpp_refl_0000 f))) (TAlphaWff.neg (TAlphaWff.neg (nb056_split_alpha_0000 f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0013 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)), ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)), ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_019), (nb056_alpha_dummy_020 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_cnnc) (nb056_wpp_refl_0002 f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0013 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0013 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)), ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)), ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_019), (nb056_alpha_dummy_020 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_cnnc) (nb056_wpp_refl_0002 f))))))))))))))))))

theorem nb056_compact_fv_empty_0032 : (nb056_alpha_dummy_047) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0090 : (nb056_alpha_dummy_047) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_047, fv_syn_c1c] using (nb056_compact_fv_empty_0032)

theorem nb056_compact_fv_empty_0033 (f : Var) : (nb056_alpha_dummy_048 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0091 (f : Var) : (nb056_alpha_dummy_048 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_048, fv_syn_c1c] using (nb056_compact_fv_empty_0033 f)

theorem nb056_compact_fv_empty_0034 : (nb056_alpha_dummy_045) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0092 : (nb056_alpha_dummy_045) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_045, fv_syn_c1c] using (nb056_compact_fv_empty_0034)

theorem nb056_compact_fv_empty_0035 (f : Var) : (nb056_alpha_dummy_046 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0093 (f : Var) : (nb056_alpha_dummy_046 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_046, fv_syn_c1c] using (nb056_compact_fv_empty_0035 f)

theorem nb056_compact_fv_empty_0036 : (nb056_alpha_dummy_043) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0094 : (nb056_alpha_dummy_043) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_043, fv_syn_c1c] using (nb056_compact_fv_empty_0036)

theorem nb056_compact_fv_empty_0037 (f : Var) : (nb056_alpha_dummy_044 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0095 (f : Var) : (nb056_alpha_dummy_044 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_044, fv_syn_c1c] using (nb056_compact_fv_empty_0037 f)

theorem nb056_compact_envfresh_0003 (f : Var) : TEnvFresh [((nb056_alpha_dummy_029), (nb056_alpha_dummy_032 f)), ((nb056_alpha_dummy_028), (nb056_alpha_dummy_031 f)), ((nb056_alpha_dummy_027), (nb056_alpha_dummy_030 f)), ((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)), ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)), ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)), ((nb056_alpha_dummy_047), (nb056_alpha_dummy_048 f)), ((nb056_alpha_dummy_045), (nb056_alpha_dummy_046 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb056_alpha_dummy_029) (nb056_alpha_dummy_032 f) (nb056_wpp_notmem_0000) (nb056_wpp_notmem_0001 f) (TEnvFresh.consFresh (nb056_alpha_dummy_028) (nb056_alpha_dummy_031 f) (nb056_wpp_notmem_0002) (nb056_wpp_notmem_0003 f) (TEnvFresh.consFresh (nb056_alpha_dummy_027) (nb056_alpha_dummy_030 f) (nb056_wpp_notmem_0004) (nb056_wpp_notmem_0005 f) (TEnvFresh.consFresh (nb056_alpha_dummy_025) (nb056_alpha_dummy_026 f) (nb056_wpp_notmem_0006) (nb056_wpp_notmem_0007 f) (TEnvFresh.consFresh (nb056_alpha_dummy_021) (nb056_alpha_dummy_023 f) (nb056_wpp_notmem_0008) (nb056_wpp_notmem_0009 f) (TEnvFresh.consFresh (nb056_alpha_dummy_022) (nb056_alpha_dummy_024 f) (nb056_wpp_notmem_0010) (nb056_wpp_notmem_0011 f) (TEnvFresh.consFresh (nb056_alpha_dummy_047) (nb056_alpha_dummy_048 f) (nb056_wpp_notmem_0090) (nb056_wpp_notmem_0091 f) (TEnvFresh.consFresh (nb056_alpha_dummy_045) (nb056_alpha_dummy_046 f) (nb056_wpp_notmem_0092) (nb056_wpp_notmem_0093 f) (TEnvFresh.consFresh (nb056_alpha_dummy_014) (nb056_alpha_dummy_016 f) (nb056_wpp_notmem_0012) (nb056_wpp_notmem_0013 f) (TEnvFresh.consFresh (nb056_alpha_dummy_013) (nb056_alpha_dummy_015 f) (nb056_wpp_notmem_0014) (nb056_wpp_notmem_0015 f) (TEnvFresh.consFresh (nb056_alpha_dummy_043) (nb056_alpha_dummy_044 f) (nb056_wpp_notmem_0094) (nb056_wpp_notmem_0095 f) (TEnvFresh.consFresh (nb056_alpha_dummy_017) (nb056_alpha_dummy_018 f) (nb056_wpp_notmem_0018) (nb056_wpp_notmem_0019 f) (TEnvFresh.consFresh (nb056_alpha_dummy_006) (nb056_alpha_dummy_009 f) (nb056_wpp_notmem_0020) (nb056_wpp_notmem_0021 f) (TEnvFresh.consFresh (nb056_alpha_dummy_005) (nb056_alpha_dummy_008 f) (nb056_wpp_notmem_0022) (nb056_wpp_notmem_0023 f) (TEnvFresh.consFresh (nb056_alpha_dummy_011) (nb056_alpha_dummy_012 f) (nb056_wpp_notmem_0024) (nb056_wpp_notmem_0025 f) (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f) (nb056_wpp_notmem_0026) (nb056_wpp_notmem_0027 f) (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f) (nb056_wpp_notmem_0028) (nb056_wpp_notmem_0029 f) (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0030) (nb056_wpp_notmem_0031 f) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))

noncomputable def nb056_wpp_refl_0003 (f : Var) : TReflOn [((nb056_alpha_dummy_029), (nb056_alpha_dummy_032 f)), ((nb056_alpha_dummy_028), (nb056_alpha_dummy_031 f)), ((nb056_alpha_dummy_027), (nb056_alpha_dummy_030 f)), ((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)), ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)), ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)), ((nb056_alpha_dummy_047), (nb056_alpha_dummy_048 f)), ((nb056_alpha_dummy_045), (nb056_alpha_dummy_046 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0003 f)

theorem nb056_wpp_notmem_0096 : (nb056_alpha_dummy_047) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_047, fv_syn_c0] using (nb056_compact_fv_empty_0032)

theorem nb056_wpp_notmem_0097 (f : Var) : (nb056_alpha_dummy_048 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_048, fv_syn_c0] using (nb056_compact_fv_empty_0033 f)

theorem nb056_wpp_notmem_0098 : (nb056_alpha_dummy_045) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_045, fv_syn_c0] using (nb056_compact_fv_empty_0034)

theorem nb056_wpp_notmem_0099 (f : Var) : (nb056_alpha_dummy_046 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_046, fv_syn_c0] using (nb056_compact_fv_empty_0035 f)

theorem nb056_wpp_notmem_0100 : (nb056_alpha_dummy_043) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_043, fv_syn_c0] using (nb056_compact_fv_empty_0036)

theorem nb056_wpp_notmem_0101 (f : Var) : (nb056_alpha_dummy_044 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_044, fv_syn_c0] using (nb056_compact_fv_empty_0037 f)

theorem nb056_compact_envfresh_0004 (f : Var) : TEnvFresh [((nb056_alpha_dummy_029), (nb056_alpha_dummy_032 f)), ((nb056_alpha_dummy_028), (nb056_alpha_dummy_031 f)), ((nb056_alpha_dummy_027), (nb056_alpha_dummy_030 f)), ((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)), ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)), ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)), ((nb056_alpha_dummy_047), (nb056_alpha_dummy_048 f)), ((nb056_alpha_dummy_045), (nb056_alpha_dummy_046 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb056_alpha_dummy_029) (nb056_alpha_dummy_032 f) (nb056_wpp_notmem_0032) (nb056_wpp_notmem_0033 f) (TEnvFresh.consFresh (nb056_alpha_dummy_028) (nb056_alpha_dummy_031 f) (nb056_wpp_notmem_0034) (nb056_wpp_notmem_0035 f) (TEnvFresh.consFresh (nb056_alpha_dummy_027) (nb056_alpha_dummy_030 f) (nb056_wpp_notmem_0036) (nb056_wpp_notmem_0037 f) (TEnvFresh.consFresh (nb056_alpha_dummy_025) (nb056_alpha_dummy_026 f) (nb056_wpp_notmem_0038) (nb056_wpp_notmem_0039 f) (TEnvFresh.consFresh (nb056_alpha_dummy_021) (nb056_alpha_dummy_023 f) (nb056_wpp_notmem_0040) (nb056_wpp_notmem_0041 f) (TEnvFresh.consFresh (nb056_alpha_dummy_022) (nb056_alpha_dummy_024 f) (nb056_wpp_notmem_0042) (nb056_wpp_notmem_0043 f) (TEnvFresh.consFresh (nb056_alpha_dummy_047) (nb056_alpha_dummy_048 f) (nb056_wpp_notmem_0096) (nb056_wpp_notmem_0097 f) (TEnvFresh.consFresh (nb056_alpha_dummy_045) (nb056_alpha_dummy_046 f) (nb056_wpp_notmem_0098) (nb056_wpp_notmem_0099 f) (TEnvFresh.consFresh (nb056_alpha_dummy_014) (nb056_alpha_dummy_016 f) (nb056_wpp_notmem_0044) (nb056_wpp_notmem_0045 f) (TEnvFresh.consFresh (nb056_alpha_dummy_013) (nb056_alpha_dummy_015 f) (nb056_wpp_notmem_0046) (nb056_wpp_notmem_0047 f) (TEnvFresh.consFresh (nb056_alpha_dummy_043) (nb056_alpha_dummy_044 f) (nb056_wpp_notmem_0100) (nb056_wpp_notmem_0101 f) (TEnvFresh.consFresh (nb056_alpha_dummy_017) (nb056_alpha_dummy_018 f) (nb056_wpp_notmem_0050) (nb056_wpp_notmem_0051 f) (TEnvFresh.consFresh (nb056_alpha_dummy_006) (nb056_alpha_dummy_009 f) (nb056_wpp_notmem_0052) (nb056_wpp_notmem_0053 f) (TEnvFresh.consFresh (nb056_alpha_dummy_005) (nb056_alpha_dummy_008 f) (nb056_wpp_notmem_0054) (nb056_wpp_notmem_0055 f) (TEnvFresh.consFresh (nb056_alpha_dummy_011) (nb056_alpha_dummy_012 f) (nb056_wpp_notmem_0056) (nb056_wpp_notmem_0057 f) (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f) (nb056_wpp_notmem_0058) (nb056_wpp_notmem_0059 f) (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f) (nb056_wpp_notmem_0060) (nb056_wpp_notmem_0061 f) (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0062) (nb056_wpp_notmem_0063 f) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))

noncomputable def nb056_wpp_refl_0004 (f : Var) : TReflOn [((nb056_alpha_dummy_029), (nb056_alpha_dummy_032 f)), ((nb056_alpha_dummy_028), (nb056_alpha_dummy_031 f)), ((nb056_alpha_dummy_027), (nb056_alpha_dummy_030 f)), ((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)), ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)), ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)), ((nb056_alpha_dummy_047), (nb056_alpha_dummy_048 f)), ((nb056_alpha_dummy_045), (nb056_alpha_dummy_046 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0004 f)

noncomputable def nb056_split_alpha_0002 (f : Var) : TAlphaWff [((nb056_alpha_dummy_029), (nb056_alpha_dummy_032 f)), ((nb056_alpha_dummy_028), (nb056_alpha_dummy_031 f)), ((nb056_alpha_dummy_027), (nb056_alpha_dummy_030 f)), ((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)), ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)), ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)), ((nb056_alpha_dummy_047), (nb056_alpha_dummy_048 f)), ((nb056_alpha_dummy_045), (nb056_alpha_dummy_046 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb056_alpha_dummy_028)) (Class.cv (nb056_alpha_dummy_029))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_027)) (syn_cun (Class.cv (nb056_alpha_dummy_028)) (Class.cv (nb056_alpha_dummy_029)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb056_alpha_dummy_031 f)) (Class.cv (nb056_alpha_dummy_032 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_030 f)) (syn_cun (Class.cv (nb056_alpha_dummy_031 f)) (Class.cv (nb056_alpha_dummy_032 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0019 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0017 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0023 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0021 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0019 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0017 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0023 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0021 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_029), (nb056_alpha_dummy_032 f)), ((nb056_alpha_dummy_028), (nb056_alpha_dummy_031 f)), ((nb056_alpha_dummy_027), (nb056_alpha_dummy_030 f)), ((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)), ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)), ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)), ((nb056_alpha_dummy_047), (nb056_alpha_dummy_048 f)), ((nb056_alpha_dummy_045), (nb056_alpha_dummy_046 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_c0) (nb056_wpp_refl_0004 f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0027 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0025 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0027 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0025 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0031 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0029 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0031 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0029 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb056_wpp_notmem_0102 : (nb056_alpha_dummy_047) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_047, fv_syn_cnnc] using (nb056_compact_fv_empty_0032)

theorem nb056_wpp_notmem_0103 (f : Var) : (nb056_alpha_dummy_048 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_048, fv_syn_cnnc] using (nb056_compact_fv_empty_0033 f)

theorem nb056_wpp_notmem_0104 : (nb056_alpha_dummy_045) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_045, fv_syn_cnnc] using (nb056_compact_fv_empty_0034)

theorem nb056_wpp_notmem_0105 (f : Var) : (nb056_alpha_dummy_046 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_046, fv_syn_cnnc] using (nb056_compact_fv_empty_0035 f)

theorem nb056_wpp_notmem_0106 : (nb056_alpha_dummy_043) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_043, fv_syn_cnnc] using (nb056_compact_fv_empty_0036)

theorem nb056_wpp_notmem_0107 (f : Var) : (nb056_alpha_dummy_044 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_044, fv_syn_cnnc] using (nb056_compact_fv_empty_0037 f)

theorem nb056_compact_envfresh_0005 (f : Var) : TEnvFresh [((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)), ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)), ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)), ((nb056_alpha_dummy_047), (nb056_alpha_dummy_048 f)), ((nb056_alpha_dummy_045), (nb056_alpha_dummy_046 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb056_alpha_dummy_025) (nb056_alpha_dummy_026 f) (nb056_wpp_notmem_0064) (nb056_wpp_notmem_0065 f) (TEnvFresh.consFresh (nb056_alpha_dummy_021) (nb056_alpha_dummy_023 f) (nb056_wpp_notmem_0066) (nb056_wpp_notmem_0067 f) (TEnvFresh.consFresh (nb056_alpha_dummy_022) (nb056_alpha_dummy_024 f) (nb056_wpp_notmem_0068) (nb056_wpp_notmem_0069 f) (TEnvFresh.consFresh (nb056_alpha_dummy_047) (nb056_alpha_dummy_048 f) (nb056_wpp_notmem_0102) (nb056_wpp_notmem_0103 f) (TEnvFresh.consFresh (nb056_alpha_dummy_045) (nb056_alpha_dummy_046 f) (nb056_wpp_notmem_0104) (nb056_wpp_notmem_0105 f) (TEnvFresh.consFresh (nb056_alpha_dummy_014) (nb056_alpha_dummy_016 f) (nb056_wpp_notmem_0070) (nb056_wpp_notmem_0071 f) (TEnvFresh.consFresh (nb056_alpha_dummy_013) (nb056_alpha_dummy_015 f) (nb056_wpp_notmem_0072) (nb056_wpp_notmem_0073 f) (TEnvFresh.consFresh (nb056_alpha_dummy_043) (nb056_alpha_dummy_044 f) (nb056_wpp_notmem_0106) (nb056_wpp_notmem_0107 f) (TEnvFresh.consFresh (nb056_alpha_dummy_017) (nb056_alpha_dummy_018 f) (nb056_wpp_notmem_0076) (nb056_wpp_notmem_0077 f) (TEnvFresh.consFresh (nb056_alpha_dummy_006) (nb056_alpha_dummy_009 f) (nb056_wpp_notmem_0078) (nb056_wpp_notmem_0079 f) (TEnvFresh.consFresh (nb056_alpha_dummy_005) (nb056_alpha_dummy_008 f) (nb056_wpp_notmem_0080) (nb056_wpp_notmem_0081 f) (TEnvFresh.consFresh (nb056_alpha_dummy_011) (nb056_alpha_dummy_012 f) (nb056_wpp_notmem_0082) (nb056_wpp_notmem_0083 f) (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f) (nb056_wpp_notmem_0084) (nb056_wpp_notmem_0085 f) (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f) (nb056_wpp_notmem_0086) (nb056_wpp_notmem_0087 f) (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0088) (nb056_wpp_notmem_0089 f) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))

noncomputable def nb056_wpp_refl_0005 (f : Var) : TReflOn [((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)), ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)), ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)), ((nb056_alpha_dummy_047), (nb056_alpha_dummy_048 f)), ((nb056_alpha_dummy_045), (nb056_alpha_dummy_046 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0005 f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
