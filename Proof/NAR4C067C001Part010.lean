import NAR4C067C001Part009

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

theorem nb067_wpp_notmem_0042 : (nb067_alpha_dummy_027) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_027, fv_syn_c0] using (nb067_compact_fv_empty_0006)

theorem nb067_wpp_notmem_0043 (x : Var) (y : Var) : (nb067_alpha_dummy_028 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_028, fv_syn_c0] using (nb067_compact_fv_empty_0007 x y)

theorem nb067_wpp_notmem_0044 : (nb067_alpha_dummy_023) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_023, fv_syn_c0] using (nb067_compact_fv_empty_0008)

theorem nb067_wpp_notmem_0045 (x : Var) (y : Var) : (nb067_alpha_dummy_025 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_025, fv_syn_c0] using (nb067_compact_fv_empty_0009 x y)

theorem nb067_wpp_notmem_0046 : (nb067_alpha_dummy_024) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_024, fv_syn_c0] using (nb067_compact_fv_empty_0010)

theorem nb067_wpp_notmem_0047 (x : Var) (y : Var) : (nb067_alpha_dummy_026 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_026, fv_syn_c0] using (nb067_compact_fv_empty_0011 x y)

theorem nb067_wpp_notmem_0048 : (nb067_alpha_dummy_016) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_016, fv_syn_c0] using (nb067_compact_fv_empty_0012)

theorem nb067_wpp_notmem_0049 (x : Var) (y : Var) : (nb067_alpha_dummy_018 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_018, fv_syn_c0] using (nb067_compact_fv_empty_0013 x y)

theorem nb067_wpp_notmem_0050 : (nb067_alpha_dummy_015) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_015, fv_syn_c0] using (nb067_compact_fv_empty_0014)

theorem nb067_wpp_notmem_0051 (x : Var) (y : Var) : (nb067_alpha_dummy_017 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_017, fv_syn_c0] using (nb067_compact_fv_empty_0015 x y)

theorem nb067_wpp_notmem_0052 : (nb067_alpha_dummy_021) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_021, fv_syn_c0] using (nb067_compact_fv_empty_0016)

theorem nb067_wpp_notmem_0053 (x : Var) (y : Var) : (nb067_alpha_dummy_022 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_022, fv_syn_c0] using (nb067_compact_fv_empty_0017 x y)

theorem nb067_wpp_notmem_0054 : (nb067_alpha_dummy_019) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_019, fv_syn_c0] using (nb067_compact_fv_empty_0018)

theorem nb067_wpp_notmem_0055 (x : Var) (y : Var) : (nb067_alpha_dummy_020 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_020, fv_syn_c0] using (nb067_compact_fv_empty_0019 x y)

theorem nb067_wpp_notmem_0056 : (nb067_alpha_dummy_008) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_008, fv_syn_c0] using (nb067_compact_fv_empty_0020)

theorem nb067_wpp_notmem_0057 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_010 x y f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_010, fv_syn_c0] using (nb067_compact_fv_empty_0021 x y f)

theorem nb067_wpp_notmem_0058 : (nb067_alpha_dummy_007) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_007, fv_syn_c0] using (nb067_compact_fv_empty_0022)

theorem nb067_wpp_notmem_0059 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_009 x y f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_009, fv_syn_c0] using (nb067_compact_fv_empty_0023 x y f)

theorem nb067_wpp_notmem_0060 : (nb067_alpha_dummy_013) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_013, fv_syn_c0] using (nb067_compact_fv_empty_0024)

theorem nb067_wpp_notmem_0061 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_014 x y f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_014, fv_syn_c0] using (nb067_compact_fv_empty_0025 x y f)

theorem nb067_wpp_notmem_0062 : (nb067_alpha_dummy_011) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_011, fv_syn_c0] using (nb067_compact_fv_empty_0026)

theorem nb067_wpp_notmem_0063 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_012 x y f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_012, fv_syn_c0] using (nb067_compact_fv_empty_0027 x y f)

theorem nb067_wpp_notmem_0064 : (nb067_alpha_dummy_003) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_003, fv_syn_c0] using (nb067_compact_fv_empty_0028)

theorem nb067_wpp_notmem_0065 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_004 x y f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_004, fv_syn_c0] using (nb067_compact_fv_empty_0029 x y f)

theorem nb067_wpp_notmem_0066 : (nb067_alpha_dummy_002) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_002, fv_syn_c0] using (nb067_compact_fv_empty_0030)

theorem nb067_wpp_notmem_0067 (y : Var) : y ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb067_compact_fv_empty_0031 y)

theorem nb067_wpp_notmem_0068 : (nb067_alpha_dummy_001) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_001, fv_syn_c0] using (nb067_compact_fv_empty_0032)

theorem nb067_wpp_notmem_0069 (x : Var) : x ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb067_compact_fv_empty_0033 x)

theorem nb067_wpp_notmem_0070 : (nb067_alpha_dummy_005) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_005, fv_syn_c0] using (nb067_compact_fv_empty_0034)

theorem nb067_wpp_notmem_0071 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_006 x y f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_006, fv_syn_c0] using (nb067_compact_fv_empty_0035 x y f)

theorem nb067_compact_envfresh_0001 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_031), (nb067_alpha_dummy_034 x y)), ((nb067_alpha_dummy_030), (nb067_alpha_dummy_033 x y)), ((nb067_alpha_dummy_029), (nb067_alpha_dummy_032 x y)), ((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)), ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)), ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)), ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)), ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)), ((nb067_alpha_dummy_021), (nb067_alpha_dummy_022 x y)), ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_031) (nb067_alpha_dummy_034 x y) (nb067_wpp_notmem_0036) (nb067_wpp_notmem_0037 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_030) (nb067_alpha_dummy_033 x y) (nb067_wpp_notmem_0038) (nb067_wpp_notmem_0039 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_029) (nb067_alpha_dummy_032 x y) (nb067_wpp_notmem_0040) (nb067_wpp_notmem_0041 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_027) (nb067_alpha_dummy_028 x y) (nb067_wpp_notmem_0042) (nb067_wpp_notmem_0043 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_023) (nb067_alpha_dummy_025 x y) (nb067_wpp_notmem_0044) (nb067_wpp_notmem_0045 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_024) (nb067_alpha_dummy_026 x y) (nb067_wpp_notmem_0046) (nb067_wpp_notmem_0047 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_016) (nb067_alpha_dummy_018 x y) (nb067_wpp_notmem_0048) (nb067_wpp_notmem_0049 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_015) (nb067_alpha_dummy_017 x y) (nb067_wpp_notmem_0050) (nb067_wpp_notmem_0051 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_021) (nb067_alpha_dummy_022 x y) (nb067_wpp_notmem_0052) (nb067_wpp_notmem_0053 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_019) (nb067_alpha_dummy_020 x y) (nb067_wpp_notmem_0054) (nb067_wpp_notmem_0055 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_008) (nb067_alpha_dummy_010 x y f) (nb067_wpp_notmem_0056) (nb067_wpp_notmem_0057 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_007) (nb067_alpha_dummy_009 x y f) (nb067_wpp_notmem_0058) (nb067_wpp_notmem_0059 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_013) (nb067_alpha_dummy_014 x y f) (nb067_wpp_notmem_0060) (nb067_wpp_notmem_0061 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_011) (nb067_alpha_dummy_012 x y f) (nb067_wpp_notmem_0062) (nb067_wpp_notmem_0063 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0064) (nb067_wpp_notmem_0065 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0066) (nb067_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0068) (nb067_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0070) (nb067_wpp_notmem_0071 x y f) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))

noncomputable def nb067_wpp_refl_0001 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_031), (nb067_alpha_dummy_034 x y)), ((nb067_alpha_dummy_030), (nb067_alpha_dummy_033 x y)), ((nb067_alpha_dummy_029), (nb067_alpha_dummy_032 x y)), ((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)), ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)), ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)), ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)), ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)), ((nb067_alpha_dummy_021), (nb067_alpha_dummy_022 x y)), ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0001 x y f)

noncomputable def nb067_split_alpha_0000 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb067_alpha_dummy_031), (nb067_alpha_dummy_034 x y)), ((nb067_alpha_dummy_030), (nb067_alpha_dummy_033 x y)), ((nb067_alpha_dummy_029), (nb067_alpha_dummy_032 x y)), ((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)), ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)), ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)), ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)), ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)), ((nb067_alpha_dummy_021), (nb067_alpha_dummy_022 x y)), ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_030)) (Class.cv (nb067_alpha_dummy_031))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_029)) (syn_cun (Class.cv (nb067_alpha_dummy_030)) (Class.cv (nb067_alpha_dummy_031)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_033 x y)) (Class.cv (nb067_alpha_dummy_034 x y))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_032 x y)) (syn_cun (Class.cv (nb067_alpha_dummy_033 x y)) (Class.cv (nb067_alpha_dummy_034 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0029 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0027 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0033 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0031 x y) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0029 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0027 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0033 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0031 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_031), (nb067_alpha_dummy_034 x y)), ((nb067_alpha_dummy_030), (nb067_alpha_dummy_033 x y)), ((nb067_alpha_dummy_029), (nb067_alpha_dummy_032 x y)), ((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)), ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)), ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)), ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)), ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)), ((nb067_alpha_dummy_021), (nb067_alpha_dummy_022 x y)), ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_c0) (nb067_wpp_refl_0001 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0036) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0037 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0034) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0035 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0036) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0037 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0034) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0035 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0040) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0041 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0038) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0039 x y) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0040) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0041 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0038) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0039 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb067_wpp_notmem_0072 : (nb067_alpha_dummy_027) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_027, fv_syn_cnnc] using (nb067_compact_fv_empty_0006)

theorem nb067_wpp_notmem_0073 (x : Var) (y : Var) : (nb067_alpha_dummy_028 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_028, fv_syn_cnnc] using (nb067_compact_fv_empty_0007 x y)

theorem nb067_wpp_notmem_0074 : (nb067_alpha_dummy_023) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_023, fv_syn_cnnc] using (nb067_compact_fv_empty_0008)

theorem nb067_wpp_notmem_0075 (x : Var) (y : Var) : (nb067_alpha_dummy_025 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_025, fv_syn_cnnc] using (nb067_compact_fv_empty_0009 x y)

theorem nb067_wpp_notmem_0076 : (nb067_alpha_dummy_024) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_024, fv_syn_cnnc] using (nb067_compact_fv_empty_0010)

theorem nb067_wpp_notmem_0077 (x : Var) (y : Var) : (nb067_alpha_dummy_026 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_026, fv_syn_cnnc] using (nb067_compact_fv_empty_0011 x y)

theorem nb067_wpp_notmem_0078 : (nb067_alpha_dummy_016) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_016, fv_syn_cnnc] using (nb067_compact_fv_empty_0012)

theorem nb067_wpp_notmem_0079 (x : Var) (y : Var) : (nb067_alpha_dummy_018 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_018, fv_syn_cnnc] using (nb067_compact_fv_empty_0013 x y)

theorem nb067_wpp_notmem_0080 : (nb067_alpha_dummy_015) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_015, fv_syn_cnnc] using (nb067_compact_fv_empty_0014)

theorem nb067_wpp_notmem_0081 (x : Var) (y : Var) : (nb067_alpha_dummy_017 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_017, fv_syn_cnnc] using (nb067_compact_fv_empty_0015 x y)

theorem nb067_wpp_notmem_0082 : (nb067_alpha_dummy_021) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_021, fv_syn_cnnc] using (nb067_compact_fv_empty_0016)

theorem nb067_wpp_notmem_0083 (x : Var) (y : Var) : (nb067_alpha_dummy_022 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_022, fv_syn_cnnc] using (nb067_compact_fv_empty_0017 x y)

theorem nb067_wpp_notmem_0084 : (nb067_alpha_dummy_019) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_019, fv_syn_cnnc] using (nb067_compact_fv_empty_0018)

theorem nb067_wpp_notmem_0085 (x : Var) (y : Var) : (nb067_alpha_dummy_020 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_020, fv_syn_cnnc] using (nb067_compact_fv_empty_0019 x y)

theorem nb067_wpp_notmem_0086 : (nb067_alpha_dummy_008) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_008, fv_syn_cnnc] using (nb067_compact_fv_empty_0020)

theorem nb067_wpp_notmem_0087 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_010 x y f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_010, fv_syn_cnnc] using (nb067_compact_fv_empty_0021 x y f)

theorem nb067_wpp_notmem_0088 : (nb067_alpha_dummy_007) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_007, fv_syn_cnnc] using (nb067_compact_fv_empty_0022)

theorem nb067_wpp_notmem_0089 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_009 x y f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_009, fv_syn_cnnc] using (nb067_compact_fv_empty_0023 x y f)

theorem nb067_wpp_notmem_0090 : (nb067_alpha_dummy_013) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_013, fv_syn_cnnc] using (nb067_compact_fv_empty_0024)

theorem nb067_wpp_notmem_0091 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_014 x y f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_014, fv_syn_cnnc] using (nb067_compact_fv_empty_0025 x y f)

theorem nb067_wpp_notmem_0092 : (nb067_alpha_dummy_011) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_011, fv_syn_cnnc] using (nb067_compact_fv_empty_0026)

theorem nb067_wpp_notmem_0093 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_012 x y f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_012, fv_syn_cnnc] using (nb067_compact_fv_empty_0027 x y f)

theorem nb067_wpp_notmem_0094 : (nb067_alpha_dummy_003) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_003, fv_syn_cnnc] using (nb067_compact_fv_empty_0028)

theorem nb067_wpp_notmem_0095 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_004 x y f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_004, fv_syn_cnnc] using (nb067_compact_fv_empty_0029 x y f)

theorem nb067_wpp_notmem_0096 : (nb067_alpha_dummy_002) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_002, fv_syn_cnnc] using (nb067_compact_fv_empty_0030)

theorem nb067_wpp_notmem_0097 (y : Var) : y ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb067_compact_fv_empty_0031 y)

theorem nb067_wpp_notmem_0098 : (nb067_alpha_dummy_001) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_001, fv_syn_cnnc] using (nb067_compact_fv_empty_0032)

theorem nb067_wpp_notmem_0099 (x : Var) : x ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb067_compact_fv_empty_0033 x)

theorem nb067_wpp_notmem_0100 : (nb067_alpha_dummy_005) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_005, fv_syn_cnnc] using (nb067_compact_fv_empty_0034)

theorem nb067_wpp_notmem_0101 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_006 x y f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_006, fv_syn_cnnc] using (nb067_compact_fv_empty_0035 x y f)

theorem nb067_compact_envfresh_0002 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)), ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)), ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)), ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)), ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)), ((nb067_alpha_dummy_021), (nb067_alpha_dummy_022 x y)), ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_027) (nb067_alpha_dummy_028 x y) (nb067_wpp_notmem_0072) (nb067_wpp_notmem_0073 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_023) (nb067_alpha_dummy_025 x y) (nb067_wpp_notmem_0074) (nb067_wpp_notmem_0075 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_024) (nb067_alpha_dummy_026 x y) (nb067_wpp_notmem_0076) (nb067_wpp_notmem_0077 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_016) (nb067_alpha_dummy_018 x y) (nb067_wpp_notmem_0078) (nb067_wpp_notmem_0079 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_015) (nb067_alpha_dummy_017 x y) (nb067_wpp_notmem_0080) (nb067_wpp_notmem_0081 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_021) (nb067_alpha_dummy_022 x y) (nb067_wpp_notmem_0082) (nb067_wpp_notmem_0083 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_019) (nb067_alpha_dummy_020 x y) (nb067_wpp_notmem_0084) (nb067_wpp_notmem_0085 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_008) (nb067_alpha_dummy_010 x y f) (nb067_wpp_notmem_0086) (nb067_wpp_notmem_0087 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_007) (nb067_alpha_dummy_009 x y f) (nb067_wpp_notmem_0088) (nb067_wpp_notmem_0089 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_013) (nb067_alpha_dummy_014 x y f) (nb067_wpp_notmem_0090) (nb067_wpp_notmem_0091 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_011) (nb067_alpha_dummy_012 x y f) (nb067_wpp_notmem_0092) (nb067_wpp_notmem_0093 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0094) (nb067_wpp_notmem_0095 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0096) (nb067_wpp_notmem_0097 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0098) (nb067_wpp_notmem_0099 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0100) (nb067_wpp_notmem_0101 x y f) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))

noncomputable def nb067_wpp_refl_0002 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)), ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)), ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)), ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)), ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)), ((nb067_alpha_dummy_021), (nb067_alpha_dummy_022 x y)), ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0002 x y f)

noncomputable def nb067_split_alpha_0001 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)), ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)), ((nb067_alpha_dummy_021), (nb067_alpha_dummy_022 x y)), ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cphi (Class.cv (nb067_alpha_dummy_016)))) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_001))).fv ∪ ((Class.cv (nb067_alpha_dummy_002))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0021 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0020) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0021 x y) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_016))).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_018 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0024) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0025 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0025 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0023 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_031), (nb067_alpha_dummy_034 x y)), ((nb067_alpha_dummy_030), (nb067_alpha_dummy_033 x y)), ((nb067_alpha_dummy_029), (nb067_alpha_dummy_032 x y)), ((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)), ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)), ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)), ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)), ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)), ((nb067_alpha_dummy_021), (nb067_alpha_dummy_022 x y)), ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_c1c) (nb067_wpp_refl_0000 x y f))) (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0000 x y f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0023 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)), ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)), ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)), ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)), ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)), ((nb067_alpha_dummy_021), (nb067_alpha_dummy_022 x y)), ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_cnnc) (nb067_wpp_refl_0002 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0023 x y) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0023 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)), ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)), ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)), ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)), ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)), ((nb067_alpha_dummy_021), (nb067_alpha_dummy_022 x y)), ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_cnnc) (nb067_wpp_refl_0002 x y f))))))))))))))))))

theorem nb067_compact_fv_empty_0036 : (nb067_alpha_dummy_049) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0102 : (nb067_alpha_dummy_049) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_049, fv_syn_c1c] using (nb067_compact_fv_empty_0036)

theorem nb067_compact_fv_empty_0037 (x : Var) (y : Var) : (nb067_alpha_dummy_050 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0103 (x : Var) (y : Var) : (nb067_alpha_dummy_050 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_050, fv_syn_c1c] using (nb067_compact_fv_empty_0037 x y)

theorem nb067_compact_fv_empty_0038 : (nb067_alpha_dummy_047) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0104 : (nb067_alpha_dummy_047) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_047, fv_syn_c1c] using (nb067_compact_fv_empty_0038)

theorem nb067_compact_fv_empty_0039 (x : Var) (y : Var) : (nb067_alpha_dummy_048 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0105 (x : Var) (y : Var) : (nb067_alpha_dummy_048 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_048, fv_syn_c1c] using (nb067_compact_fv_empty_0039 x y)

theorem nb067_compact_fv_empty_0040 : (nb067_alpha_dummy_045) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0106 : (nb067_alpha_dummy_045) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_045, fv_syn_c1c] using (nb067_compact_fv_empty_0040)

theorem nb067_compact_fv_empty_0041 (x : Var) (y : Var) : (nb067_alpha_dummy_046 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0107 (x : Var) (y : Var) : (nb067_alpha_dummy_046 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_046, fv_syn_c1c] using (nb067_compact_fv_empty_0041 x y)

theorem nb067_compact_envfresh_0003 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_031), (nb067_alpha_dummy_034 x y)), ((nb067_alpha_dummy_030), (nb067_alpha_dummy_033 x y)), ((nb067_alpha_dummy_029), (nb067_alpha_dummy_032 x y)), ((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)), ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)), ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)), ((nb067_alpha_dummy_049), (nb067_alpha_dummy_050 x y)), ((nb067_alpha_dummy_047), (nb067_alpha_dummy_048 x y)), ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)), ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)), ((nb067_alpha_dummy_045), (nb067_alpha_dummy_046 x y)), ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_031) (nb067_alpha_dummy_034 x y) (nb067_wpp_notmem_0000) (nb067_wpp_notmem_0001 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_030) (nb067_alpha_dummy_033 x y) (nb067_wpp_notmem_0002) (nb067_wpp_notmem_0003 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_029) (nb067_alpha_dummy_032 x y) (nb067_wpp_notmem_0004) (nb067_wpp_notmem_0005 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_027) (nb067_alpha_dummy_028 x y) (nb067_wpp_notmem_0006) (nb067_wpp_notmem_0007 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_023) (nb067_alpha_dummy_025 x y) (nb067_wpp_notmem_0008) (nb067_wpp_notmem_0009 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_024) (nb067_alpha_dummy_026 x y) (nb067_wpp_notmem_0010) (nb067_wpp_notmem_0011 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_049) (nb067_alpha_dummy_050 x y) (nb067_wpp_notmem_0102) (nb067_wpp_notmem_0103 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_047) (nb067_alpha_dummy_048 x y) (nb067_wpp_notmem_0104) (nb067_wpp_notmem_0105 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_016) (nb067_alpha_dummy_018 x y) (nb067_wpp_notmem_0012) (nb067_wpp_notmem_0013 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_015) (nb067_alpha_dummy_017 x y) (nb067_wpp_notmem_0014) (nb067_wpp_notmem_0015 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_045) (nb067_alpha_dummy_046 x y) (nb067_wpp_notmem_0106) (nb067_wpp_notmem_0107 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_019) (nb067_alpha_dummy_020 x y) (nb067_wpp_notmem_0018) (nb067_wpp_notmem_0019 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_008) (nb067_alpha_dummy_010 x y f) (nb067_wpp_notmem_0020) (nb067_wpp_notmem_0021 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_007) (nb067_alpha_dummy_009 x y f) (nb067_wpp_notmem_0022) (nb067_wpp_notmem_0023 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_013) (nb067_alpha_dummy_014 x y f) (nb067_wpp_notmem_0024) (nb067_wpp_notmem_0025 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_011) (nb067_alpha_dummy_012 x y f) (nb067_wpp_notmem_0026) (nb067_wpp_notmem_0027 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0028) (nb067_wpp_notmem_0029 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0030) (nb067_wpp_notmem_0031 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0032) (nb067_wpp_notmem_0033 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0034) (nb067_wpp_notmem_0035 x y f) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))

noncomputable def nb067_wpp_refl_0003 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_031), (nb067_alpha_dummy_034 x y)), ((nb067_alpha_dummy_030), (nb067_alpha_dummy_033 x y)), ((nb067_alpha_dummy_029), (nb067_alpha_dummy_032 x y)), ((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)), ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)), ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)), ((nb067_alpha_dummy_049), (nb067_alpha_dummy_050 x y)), ((nb067_alpha_dummy_047), (nb067_alpha_dummy_048 x y)), ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)), ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)), ((nb067_alpha_dummy_045), (nb067_alpha_dummy_046 x y)), ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0003 x y f)

theorem nb067_wpp_notmem_0108 : (nb067_alpha_dummy_049) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_049, fv_syn_c0] using (nb067_compact_fv_empty_0036)

theorem nb067_wpp_notmem_0109 (x : Var) (y : Var) : (nb067_alpha_dummy_050 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_050, fv_syn_c0] using (nb067_compact_fv_empty_0037 x y)

theorem nb067_wpp_notmem_0110 : (nb067_alpha_dummy_047) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_047, fv_syn_c0] using (nb067_compact_fv_empty_0038)

theorem nb067_wpp_notmem_0111 (x : Var) (y : Var) : (nb067_alpha_dummy_048 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_048, fv_syn_c0] using (nb067_compact_fv_empty_0039 x y)

theorem nb067_wpp_notmem_0112 : (nb067_alpha_dummy_045) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_045, fv_syn_c0] using (nb067_compact_fv_empty_0040)

theorem nb067_wpp_notmem_0113 (x : Var) (y : Var) : (nb067_alpha_dummy_046 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_046, fv_syn_c0] using (nb067_compact_fv_empty_0041 x y)

theorem nb067_compact_envfresh_0004 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_031), (nb067_alpha_dummy_034 x y)), ((nb067_alpha_dummy_030), (nb067_alpha_dummy_033 x y)), ((nb067_alpha_dummy_029), (nb067_alpha_dummy_032 x y)), ((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)), ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)), ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)), ((nb067_alpha_dummy_049), (nb067_alpha_dummy_050 x y)), ((nb067_alpha_dummy_047), (nb067_alpha_dummy_048 x y)), ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)), ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)), ((nb067_alpha_dummy_045), (nb067_alpha_dummy_046 x y)), ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_031) (nb067_alpha_dummy_034 x y) (nb067_wpp_notmem_0036) (nb067_wpp_notmem_0037 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_030) (nb067_alpha_dummy_033 x y) (nb067_wpp_notmem_0038) (nb067_wpp_notmem_0039 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_029) (nb067_alpha_dummy_032 x y) (nb067_wpp_notmem_0040) (nb067_wpp_notmem_0041 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_027) (nb067_alpha_dummy_028 x y) (nb067_wpp_notmem_0042) (nb067_wpp_notmem_0043 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_023) (nb067_alpha_dummy_025 x y) (nb067_wpp_notmem_0044) (nb067_wpp_notmem_0045 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_024) (nb067_alpha_dummy_026 x y) (nb067_wpp_notmem_0046) (nb067_wpp_notmem_0047 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_049) (nb067_alpha_dummy_050 x y) (nb067_wpp_notmem_0108) (nb067_wpp_notmem_0109 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_047) (nb067_alpha_dummy_048 x y) (nb067_wpp_notmem_0110) (nb067_wpp_notmem_0111 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_016) (nb067_alpha_dummy_018 x y) (nb067_wpp_notmem_0048) (nb067_wpp_notmem_0049 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_015) (nb067_alpha_dummy_017 x y) (nb067_wpp_notmem_0050) (nb067_wpp_notmem_0051 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_045) (nb067_alpha_dummy_046 x y) (nb067_wpp_notmem_0112) (nb067_wpp_notmem_0113 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_019) (nb067_alpha_dummy_020 x y) (nb067_wpp_notmem_0054) (nb067_wpp_notmem_0055 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_008) (nb067_alpha_dummy_010 x y f) (nb067_wpp_notmem_0056) (nb067_wpp_notmem_0057 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_007) (nb067_alpha_dummy_009 x y f) (nb067_wpp_notmem_0058) (nb067_wpp_notmem_0059 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_013) (nb067_alpha_dummy_014 x y f) (nb067_wpp_notmem_0060) (nb067_wpp_notmem_0061 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_011) (nb067_alpha_dummy_012 x y f) (nb067_wpp_notmem_0062) (nb067_wpp_notmem_0063 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0064) (nb067_wpp_notmem_0065 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0066) (nb067_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0068) (nb067_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0070) (nb067_wpp_notmem_0071 x y f) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))

noncomputable def nb067_wpp_refl_0004 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_031), (nb067_alpha_dummy_034 x y)), ((nb067_alpha_dummy_030), (nb067_alpha_dummy_033 x y)), ((nb067_alpha_dummy_029), (nb067_alpha_dummy_032 x y)), ((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)), ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)), ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)), ((nb067_alpha_dummy_049), (nb067_alpha_dummy_050 x y)), ((nb067_alpha_dummy_047), (nb067_alpha_dummy_048 x y)), ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)), ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)), ((nb067_alpha_dummy_045), (nb067_alpha_dummy_046 x y)), ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0004 x y f)

noncomputable def nb067_split_alpha_0002 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb067_alpha_dummy_031), (nb067_alpha_dummy_034 x y)), ((nb067_alpha_dummy_030), (nb067_alpha_dummy_033 x y)), ((nb067_alpha_dummy_029), (nb067_alpha_dummy_032 x y)), ((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)), ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)), ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)), ((nb067_alpha_dummy_049), (nb067_alpha_dummy_050 x y)), ((nb067_alpha_dummy_047), (nb067_alpha_dummy_048 x y)), ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)), ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)), ((nb067_alpha_dummy_045), (nb067_alpha_dummy_046 x y)), ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_030)) (Class.cv (nb067_alpha_dummy_031))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_029)) (syn_cun (Class.cv (nb067_alpha_dummy_030)) (Class.cv (nb067_alpha_dummy_031)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_033 x y)) (Class.cv (nb067_alpha_dummy_034 x y))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_032 x y)) (syn_cun (Class.cv (nb067_alpha_dummy_033 x y)) (Class.cv (nb067_alpha_dummy_034 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0029 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0027 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0033 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0031 x y) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0029 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0027 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0033 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0031 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_031), (nb067_alpha_dummy_034 x y)), ((nb067_alpha_dummy_030), (nb067_alpha_dummy_033 x y)), ((nb067_alpha_dummy_029), (nb067_alpha_dummy_032 x y)), ((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)), ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)), ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)), ((nb067_alpha_dummy_049), (nb067_alpha_dummy_050 x y)), ((nb067_alpha_dummy_047), (nb067_alpha_dummy_048 x y)), ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)), ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)), ((nb067_alpha_dummy_045), (nb067_alpha_dummy_046 x y)), ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_c0) (nb067_wpp_refl_0004 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0036) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0037 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0034) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0035 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0036) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0037 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0034) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0035 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0040) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0041 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0038) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0039 x y) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0040) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0041 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0038) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0039 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb067_wpp_notmem_0114 : (nb067_alpha_dummy_049) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_049, fv_syn_cnnc] using (nb067_compact_fv_empty_0036)

theorem nb067_wpp_notmem_0115 (x : Var) (y : Var) : (nb067_alpha_dummy_050 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_050, fv_syn_cnnc] using (nb067_compact_fv_empty_0037 x y)

theorem nb067_wpp_notmem_0116 : (nb067_alpha_dummy_047) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_047, fv_syn_cnnc] using (nb067_compact_fv_empty_0038)

theorem nb067_wpp_notmem_0117 (x : Var) (y : Var) : (nb067_alpha_dummy_048 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_048, fv_syn_cnnc] using (nb067_compact_fv_empty_0039 x y)

theorem nb067_wpp_notmem_0118 : (nb067_alpha_dummy_045) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_045, fv_syn_cnnc] using (nb067_compact_fv_empty_0040)

theorem nb067_wpp_notmem_0119 (x : Var) (y : Var) : (nb067_alpha_dummy_046 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_046, fv_syn_cnnc] using (nb067_compact_fv_empty_0041 x y)

theorem nb067_compact_envfresh_0005 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)), ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)), ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)), ((nb067_alpha_dummy_049), (nb067_alpha_dummy_050 x y)), ((nb067_alpha_dummy_047), (nb067_alpha_dummy_048 x y)), ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)), ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)), ((nb067_alpha_dummy_045), (nb067_alpha_dummy_046 x y)), ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_027) (nb067_alpha_dummy_028 x y) (nb067_wpp_notmem_0072) (nb067_wpp_notmem_0073 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_023) (nb067_alpha_dummy_025 x y) (nb067_wpp_notmem_0074) (nb067_wpp_notmem_0075 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_024) (nb067_alpha_dummy_026 x y) (nb067_wpp_notmem_0076) (nb067_wpp_notmem_0077 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_049) (nb067_alpha_dummy_050 x y) (nb067_wpp_notmem_0114) (nb067_wpp_notmem_0115 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_047) (nb067_alpha_dummy_048 x y) (nb067_wpp_notmem_0116) (nb067_wpp_notmem_0117 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_016) (nb067_alpha_dummy_018 x y) (nb067_wpp_notmem_0078) (nb067_wpp_notmem_0079 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_015) (nb067_alpha_dummy_017 x y) (nb067_wpp_notmem_0080) (nb067_wpp_notmem_0081 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_045) (nb067_alpha_dummy_046 x y) (nb067_wpp_notmem_0118) (nb067_wpp_notmem_0119 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_019) (nb067_alpha_dummy_020 x y) (nb067_wpp_notmem_0084) (nb067_wpp_notmem_0085 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_008) (nb067_alpha_dummy_010 x y f) (nb067_wpp_notmem_0086) (nb067_wpp_notmem_0087 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_007) (nb067_alpha_dummy_009 x y f) (nb067_wpp_notmem_0088) (nb067_wpp_notmem_0089 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_013) (nb067_alpha_dummy_014 x y f) (nb067_wpp_notmem_0090) (nb067_wpp_notmem_0091 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_011) (nb067_alpha_dummy_012 x y f) (nb067_wpp_notmem_0092) (nb067_wpp_notmem_0093 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0094) (nb067_wpp_notmem_0095 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0096) (nb067_wpp_notmem_0097 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0098) (nb067_wpp_notmem_0099 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0100) (nb067_wpp_notmem_0101 x y f) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))

noncomputable def nb067_wpp_refl_0005 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)), ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)), ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)), ((nb067_alpha_dummy_049), (nb067_alpha_dummy_050 x y)), ((nb067_alpha_dummy_047), (nb067_alpha_dummy_048 x y)), ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)), ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)), ((nb067_alpha_dummy_045), (nb067_alpha_dummy_046 x y)), ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0005 x y f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
