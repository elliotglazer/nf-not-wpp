import NAR4C078C001Part030

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

theorem nb078_support_mem_1301 (h : Var) : (nb078_alpha_dummy_1053 h) ∈ (((Class.cab (nb078_alpha_dummy_1209 h) (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1053 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1209 h) (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1053 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1298 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1298 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1302 : (nb078_alpha_dummy_1208) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1208))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1303 (h : Var) : (nb078_alpha_dummy_1210 h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1304 : (nb078_alpha_dummy_1208) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_1208)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1208)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1305 (h : Var) : (nb078_alpha_dummy_1210 h) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_compact_fv_empty_0000 : (nb078_alpha_dummy_033) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0000 : (nb078_alpha_dummy_033) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_033, fv_syn_c1c] using (nb078_compact_fv_empty_0000)

theorem nb078_compact_fv_empty_0001 (f : Var) : (nb078_alpha_dummy_036 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0001 (f : Var) : (nb078_alpha_dummy_036 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_036, fv_syn_c1c] using (nb078_compact_fv_empty_0001 f)

theorem nb078_compact_fv_empty_0002 : (nb078_alpha_dummy_032) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0002 : (nb078_alpha_dummy_032) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_032, fv_syn_c1c] using (nb078_compact_fv_empty_0002)

theorem nb078_compact_fv_empty_0003 (f : Var) : (nb078_alpha_dummy_035 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0003 (f : Var) : (nb078_alpha_dummy_035 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_035, fv_syn_c1c] using (nb078_compact_fv_empty_0003 f)

theorem nb078_compact_fv_empty_0004 : (nb078_alpha_dummy_031) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0004 : (nb078_alpha_dummy_031) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_031, fv_syn_c1c] using (nb078_compact_fv_empty_0004)

theorem nb078_compact_fv_empty_0005 (f : Var) : (nb078_alpha_dummy_034 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0005 (f : Var) : (nb078_alpha_dummy_034 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_034, fv_syn_c1c] using (nb078_compact_fv_empty_0005 f)

theorem nb078_compact_fv_empty_0006 : (nb078_alpha_dummy_029) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0006 : (nb078_alpha_dummy_029) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_029, fv_syn_c1c] using (nb078_compact_fv_empty_0006)

theorem nb078_compact_fv_empty_0007 (f : Var) : (nb078_alpha_dummy_030 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0007 (f : Var) : (nb078_alpha_dummy_030 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_030, fv_syn_c1c] using (nb078_compact_fv_empty_0007 f)

theorem nb078_compact_fv_empty_0008 : (nb078_alpha_dummy_025) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0008 : (nb078_alpha_dummy_025) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_025, fv_syn_c1c] using (nb078_compact_fv_empty_0008)

theorem nb078_compact_fv_empty_0009 (f : Var) : (nb078_alpha_dummy_027 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0009 (f : Var) : (nb078_alpha_dummy_027 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_027, fv_syn_c1c] using (nb078_compact_fv_empty_0009 f)

theorem nb078_compact_fv_empty_0010 : (nb078_alpha_dummy_026) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0010 : (nb078_alpha_dummy_026) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_026, fv_syn_c1c] using (nb078_compact_fv_empty_0010)

theorem nb078_compact_fv_empty_0011 (f : Var) : (nb078_alpha_dummy_028 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0011 (f : Var) : (nb078_alpha_dummy_028 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_028, fv_syn_c1c] using (nb078_compact_fv_empty_0011 f)

theorem nb078_compact_fv_empty_0012 : (nb078_alpha_dummy_018) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0012 : (nb078_alpha_dummy_018) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_018, fv_syn_c1c] using (nb078_compact_fv_empty_0012)

theorem nb078_compact_fv_empty_0013 (f : Var) : (nb078_alpha_dummy_020 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0013 (f : Var) : (nb078_alpha_dummy_020 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_020, fv_syn_c1c] using (nb078_compact_fv_empty_0013 f)

theorem nb078_compact_fv_empty_0014 : (nb078_alpha_dummy_017) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0014 : (nb078_alpha_dummy_017) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_017, fv_syn_c1c] using (nb078_compact_fv_empty_0014)

theorem nb078_compact_fv_empty_0015 (f : Var) : (nb078_alpha_dummy_019 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0015 (f : Var) : (nb078_alpha_dummy_019 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_019, fv_syn_c1c] using (nb078_compact_fv_empty_0015 f)

theorem nb078_compact_fv_empty_0016 : (nb078_alpha_dummy_023) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0016 : (nb078_alpha_dummy_023) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_023, fv_syn_c1c] using (nb078_compact_fv_empty_0016)

theorem nb078_compact_fv_empty_0017 (f : Var) : (nb078_alpha_dummy_024 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0017 (f : Var) : (nb078_alpha_dummy_024 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_024, fv_syn_c1c] using (nb078_compact_fv_empty_0017 f)

theorem nb078_compact_fv_empty_0018 : (nb078_alpha_dummy_021) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0018 : (nb078_alpha_dummy_021) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_021, fv_syn_c1c] using (nb078_compact_fv_empty_0018)

theorem nb078_compact_fv_empty_0019 (f : Var) : (nb078_alpha_dummy_022 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0019 (f : Var) : (nb078_alpha_dummy_022 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_022, fv_syn_c1c] using (nb078_compact_fv_empty_0019 f)

theorem nb078_compact_fv_empty_0020 : (nb078_alpha_dummy_010) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0020 : (nb078_alpha_dummy_010) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_010, fv_syn_c1c] using (nb078_compact_fv_empty_0020)

theorem nb078_compact_fv_empty_0021 (f : Var) : (nb078_alpha_dummy_013 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0021 (f : Var) : (nb078_alpha_dummy_013 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_013, fv_syn_c1c] using (nb078_compact_fv_empty_0021 f)

theorem nb078_compact_fv_empty_0022 : (nb078_alpha_dummy_009) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0022 : (nb078_alpha_dummy_009) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_009, fv_syn_c1c] using (nb078_compact_fv_empty_0022)

theorem nb078_compact_fv_empty_0023 (f : Var) : (nb078_alpha_dummy_012 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0023 (f : Var) : (nb078_alpha_dummy_012 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_012, fv_syn_c1c] using (nb078_compact_fv_empty_0023 f)

theorem nb078_compact_fv_empty_0024 : (nb078_alpha_dummy_015) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0024 : (nb078_alpha_dummy_015) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_015, fv_syn_c1c] using (nb078_compact_fv_empty_0024)

theorem nb078_compact_fv_empty_0025 (f : Var) : (nb078_alpha_dummy_016 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0025 (f : Var) : (nb078_alpha_dummy_016 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_016, fv_syn_c1c] using (nb078_compact_fv_empty_0025 f)

theorem nb078_compact_fv_empty_0026 : (nb078_alpha_dummy_007) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0026 : (nb078_alpha_dummy_007) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_007, fv_syn_c1c] using (nb078_compact_fv_empty_0026)

theorem nb078_compact_fv_empty_0027 (f : Var) : (nb078_alpha_dummy_008 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0027 (f : Var) : (nb078_alpha_dummy_008 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_008, fv_syn_c1c] using (nb078_compact_fv_empty_0027 f)

theorem nb078_compact_fv_empty_0028 : (nb078_alpha_dummy_005) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0028 : (nb078_alpha_dummy_005) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_005, fv_syn_c1c] using (nb078_compact_fv_empty_0028)

theorem nb078_compact_fv_empty_0029 (f : Var) : (nb078_alpha_dummy_006 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0029 (f : Var) : (nb078_alpha_dummy_006 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_006, fv_syn_c1c] using (nb078_compact_fv_empty_0029 f)

theorem nb078_compact_fv_empty_0030 : (nb078_alpha_dummy_000) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0030 : (nb078_alpha_dummy_000) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_000, fv_syn_c1c] using (nb078_compact_fv_empty_0030)

theorem nb078_compact_fv_empty_0031 (f : Var) : f ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0031 (f : Var) : f ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0031 f)

theorem nb078_compact_fv_empty_0032 : (nb078_alpha_dummy_004) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0032 : (nb078_alpha_dummy_004) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_004, fv_syn_c1c] using (nb078_compact_fv_empty_0032)

theorem nb078_compact_fv_empty_0033 (y : Var) : y ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0033 (y : Var) : y ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0033 y)

theorem nb078_compact_fv_empty_0034 : (nb078_alpha_dummy_003) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0034 : (nb078_alpha_dummy_003) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_003, fv_syn_c1c] using (nb078_compact_fv_empty_0034)

theorem nb078_compact_fv_empty_0035 (x : Var) : x ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0035 (x : Var) : x ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0035 x)

theorem nb078_compact_envfresh_0000 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_033), (nb078_alpha_dummy_036 f)), ((nb078_alpha_dummy_032), (nb078_alpha_dummy_035 f)), ((nb078_alpha_dummy_031), (nb078_alpha_dummy_034 f)), ((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)), ((nb078_alpha_dummy_025), (nb078_alpha_dummy_027 f)), ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)), ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)), ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)), ((nb078_alpha_dummy_023), (nb078_alpha_dummy_024 f)), ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_033) (nb078_alpha_dummy_036 f) (nb078_wpp_notmem_0000) (nb078_wpp_notmem_0001 f) (TEnvFresh.consFresh (nb078_alpha_dummy_032) (nb078_alpha_dummy_035 f) (nb078_wpp_notmem_0002) (nb078_wpp_notmem_0003 f) (TEnvFresh.consFresh (nb078_alpha_dummy_031) (nb078_alpha_dummy_034 f) (nb078_wpp_notmem_0004) (nb078_wpp_notmem_0005 f) (TEnvFresh.consFresh (nb078_alpha_dummy_029) (nb078_alpha_dummy_030 f) (nb078_wpp_notmem_0006) (nb078_wpp_notmem_0007 f) (TEnvFresh.consFresh (nb078_alpha_dummy_025) (nb078_alpha_dummy_027 f) (nb078_wpp_notmem_0008) (nb078_wpp_notmem_0009 f) (TEnvFresh.consFresh (nb078_alpha_dummy_026) (nb078_alpha_dummy_028 f) (nb078_wpp_notmem_0010) (nb078_wpp_notmem_0011 f) (TEnvFresh.consFresh (nb078_alpha_dummy_018) (nb078_alpha_dummy_020 f) (nb078_wpp_notmem_0012) (nb078_wpp_notmem_0013 f) (TEnvFresh.consFresh (nb078_alpha_dummy_017) (nb078_alpha_dummy_019 f) (nb078_wpp_notmem_0014) (nb078_wpp_notmem_0015 f) (TEnvFresh.consFresh (nb078_alpha_dummy_023) (nb078_alpha_dummy_024 f) (nb078_wpp_notmem_0016) (nb078_wpp_notmem_0017 f) (TEnvFresh.consFresh (nb078_alpha_dummy_021) (nb078_alpha_dummy_022 f) (nb078_wpp_notmem_0018) (nb078_wpp_notmem_0019 f) (TEnvFresh.consFresh (nb078_alpha_dummy_010) (nb078_alpha_dummy_013 f) (nb078_wpp_notmem_0020) (nb078_wpp_notmem_0021 f) (TEnvFresh.consFresh (nb078_alpha_dummy_009) (nb078_alpha_dummy_012 f) (nb078_wpp_notmem_0022) (nb078_wpp_notmem_0023 f) (TEnvFresh.consFresh (nb078_alpha_dummy_015) (nb078_alpha_dummy_016 f) (nb078_wpp_notmem_0024) (nb078_wpp_notmem_0025 f) (TEnvFresh.consFresh (nb078_alpha_dummy_007) (nb078_alpha_dummy_008 f) (nb078_wpp_notmem_0026) (nb078_wpp_notmem_0027 f) (TEnvFresh.consFresh (nb078_alpha_dummy_005) (nb078_alpha_dummy_006 f) (nb078_wpp_notmem_0028) (nb078_wpp_notmem_0029 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0030) (nb078_wpp_notmem_0031 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))

noncomputable def nb078_wpp_refl_0000 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_033), (nb078_alpha_dummy_036 f)), ((nb078_alpha_dummy_032), (nb078_alpha_dummy_035 f)), ((nb078_alpha_dummy_031), (nb078_alpha_dummy_034 f)), ((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)), ((nb078_alpha_dummy_025), (nb078_alpha_dummy_027 f)), ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)), ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)), ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)), ((nb078_alpha_dummy_023), (nb078_alpha_dummy_024 f)), ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0000 x y f)

theorem nb078_wpp_notmem_0036 : (nb078_alpha_dummy_033) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_033, fv_syn_c0] using (nb078_compact_fv_empty_0000)

theorem nb078_wpp_notmem_0037 (f : Var) : (nb078_alpha_dummy_036 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_036, fv_syn_c0] using (nb078_compact_fv_empty_0001 f)

theorem nb078_wpp_notmem_0038 : (nb078_alpha_dummy_032) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_032, fv_syn_c0] using (nb078_compact_fv_empty_0002)

theorem nb078_wpp_notmem_0039 (f : Var) : (nb078_alpha_dummy_035 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_035, fv_syn_c0] using (nb078_compact_fv_empty_0003 f)

theorem nb078_wpp_notmem_0040 : (nb078_alpha_dummy_031) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_031, fv_syn_c0] using (nb078_compact_fv_empty_0004)

theorem nb078_wpp_notmem_0041 (f : Var) : (nb078_alpha_dummy_034 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_034, fv_syn_c0] using (nb078_compact_fv_empty_0005 f)

theorem nb078_wpp_notmem_0042 : (nb078_alpha_dummy_029) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_029, fv_syn_c0] using (nb078_compact_fv_empty_0006)

theorem nb078_wpp_notmem_0043 (f : Var) : (nb078_alpha_dummy_030 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_030, fv_syn_c0] using (nb078_compact_fv_empty_0007 f)

theorem nb078_wpp_notmem_0044 : (nb078_alpha_dummy_025) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_025, fv_syn_c0] using (nb078_compact_fv_empty_0008)

theorem nb078_wpp_notmem_0045 (f : Var) : (nb078_alpha_dummy_027 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_027, fv_syn_c0] using (nb078_compact_fv_empty_0009 f)

theorem nb078_wpp_notmem_0046 : (nb078_alpha_dummy_026) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_026, fv_syn_c0] using (nb078_compact_fv_empty_0010)

theorem nb078_wpp_notmem_0047 (f : Var) : (nb078_alpha_dummy_028 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_028, fv_syn_c0] using (nb078_compact_fv_empty_0011 f)

theorem nb078_wpp_notmem_0048 : (nb078_alpha_dummy_018) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_018, fv_syn_c0] using (nb078_compact_fv_empty_0012)

theorem nb078_wpp_notmem_0049 (f : Var) : (nb078_alpha_dummy_020 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_020, fv_syn_c0] using (nb078_compact_fv_empty_0013 f)

theorem nb078_wpp_notmem_0050 : (nb078_alpha_dummy_017) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_017, fv_syn_c0] using (nb078_compact_fv_empty_0014)

theorem nb078_wpp_notmem_0051 (f : Var) : (nb078_alpha_dummy_019 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_019, fv_syn_c0] using (nb078_compact_fv_empty_0015 f)

theorem nb078_wpp_notmem_0052 : (nb078_alpha_dummy_023) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_023, fv_syn_c0] using (nb078_compact_fv_empty_0016)

theorem nb078_wpp_notmem_0053 (f : Var) : (nb078_alpha_dummy_024 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_024, fv_syn_c0] using (nb078_compact_fv_empty_0017 f)

theorem nb078_wpp_notmem_0054 : (nb078_alpha_dummy_021) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_021, fv_syn_c0] using (nb078_compact_fv_empty_0018)

theorem nb078_wpp_notmem_0055 (f : Var) : (nb078_alpha_dummy_022 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_022, fv_syn_c0] using (nb078_compact_fv_empty_0019 f)

theorem nb078_wpp_notmem_0056 : (nb078_alpha_dummy_010) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_010, fv_syn_c0] using (nb078_compact_fv_empty_0020)

theorem nb078_wpp_notmem_0057 (f : Var) : (nb078_alpha_dummy_013 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_013, fv_syn_c0] using (nb078_compact_fv_empty_0021 f)

theorem nb078_wpp_notmem_0058 : (nb078_alpha_dummy_009) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_009, fv_syn_c0] using (nb078_compact_fv_empty_0022)

theorem nb078_wpp_notmem_0059 (f : Var) : (nb078_alpha_dummy_012 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_012, fv_syn_c0] using (nb078_compact_fv_empty_0023 f)

theorem nb078_wpp_notmem_0060 : (nb078_alpha_dummy_015) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_015, fv_syn_c0] using (nb078_compact_fv_empty_0024)

theorem nb078_wpp_notmem_0061 (f : Var) : (nb078_alpha_dummy_016 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_016, fv_syn_c0] using (nb078_compact_fv_empty_0025 f)

theorem nb078_wpp_notmem_0062 : (nb078_alpha_dummy_007) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_007, fv_syn_c0] using (nb078_compact_fv_empty_0026)

theorem nb078_wpp_notmem_0063 (f : Var) : (nb078_alpha_dummy_008 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_008, fv_syn_c0] using (nb078_compact_fv_empty_0027 f)

theorem nb078_wpp_notmem_0064 : (nb078_alpha_dummy_005) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_005, fv_syn_c0] using (nb078_compact_fv_empty_0028)

theorem nb078_wpp_notmem_0065 (f : Var) : (nb078_alpha_dummy_006 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_006, fv_syn_c0] using (nb078_compact_fv_empty_0029 f)

theorem nb078_wpp_notmem_0066 : (nb078_alpha_dummy_000) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_000, fv_syn_c0] using (nb078_compact_fv_empty_0030)

theorem nb078_wpp_notmem_0067 (f : Var) : f ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0031 f)

theorem nb078_wpp_notmem_0068 : (nb078_alpha_dummy_004) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_004, fv_syn_c0] using (nb078_compact_fv_empty_0032)

theorem nb078_wpp_notmem_0069 (y : Var) : y ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0033 y)

theorem nb078_wpp_notmem_0070 : (nb078_alpha_dummy_003) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_003, fv_syn_c0] using (nb078_compact_fv_empty_0034)

theorem nb078_wpp_notmem_0071 (x : Var) : x ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0035 x)

theorem nb078_compact_envfresh_0001 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_033), (nb078_alpha_dummy_036 f)), ((nb078_alpha_dummy_032), (nb078_alpha_dummy_035 f)), ((nb078_alpha_dummy_031), (nb078_alpha_dummy_034 f)), ((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)), ((nb078_alpha_dummy_025), (nb078_alpha_dummy_027 f)), ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)), ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)), ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)), ((nb078_alpha_dummy_023), (nb078_alpha_dummy_024 f)), ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_033) (nb078_alpha_dummy_036 f) (nb078_wpp_notmem_0036) (nb078_wpp_notmem_0037 f) (TEnvFresh.consFresh (nb078_alpha_dummy_032) (nb078_alpha_dummy_035 f) (nb078_wpp_notmem_0038) (nb078_wpp_notmem_0039 f) (TEnvFresh.consFresh (nb078_alpha_dummy_031) (nb078_alpha_dummy_034 f) (nb078_wpp_notmem_0040) (nb078_wpp_notmem_0041 f) (TEnvFresh.consFresh (nb078_alpha_dummy_029) (nb078_alpha_dummy_030 f) (nb078_wpp_notmem_0042) (nb078_wpp_notmem_0043 f) (TEnvFresh.consFresh (nb078_alpha_dummy_025) (nb078_alpha_dummy_027 f) (nb078_wpp_notmem_0044) (nb078_wpp_notmem_0045 f) (TEnvFresh.consFresh (nb078_alpha_dummy_026) (nb078_alpha_dummy_028 f) (nb078_wpp_notmem_0046) (nb078_wpp_notmem_0047 f) (TEnvFresh.consFresh (nb078_alpha_dummy_018) (nb078_alpha_dummy_020 f) (nb078_wpp_notmem_0048) (nb078_wpp_notmem_0049 f) (TEnvFresh.consFresh (nb078_alpha_dummy_017) (nb078_alpha_dummy_019 f) (nb078_wpp_notmem_0050) (nb078_wpp_notmem_0051 f) (TEnvFresh.consFresh (nb078_alpha_dummy_023) (nb078_alpha_dummy_024 f) (nb078_wpp_notmem_0052) (nb078_wpp_notmem_0053 f) (TEnvFresh.consFresh (nb078_alpha_dummy_021) (nb078_alpha_dummy_022 f) (nb078_wpp_notmem_0054) (nb078_wpp_notmem_0055 f) (TEnvFresh.consFresh (nb078_alpha_dummy_010) (nb078_alpha_dummy_013 f) (nb078_wpp_notmem_0056) (nb078_wpp_notmem_0057 f) (TEnvFresh.consFresh (nb078_alpha_dummy_009) (nb078_alpha_dummy_012 f) (nb078_wpp_notmem_0058) (nb078_wpp_notmem_0059 f) (TEnvFresh.consFresh (nb078_alpha_dummy_015) (nb078_alpha_dummy_016 f) (nb078_wpp_notmem_0060) (nb078_wpp_notmem_0061 f) (TEnvFresh.consFresh (nb078_alpha_dummy_007) (nb078_alpha_dummy_008 f) (nb078_wpp_notmem_0062) (nb078_wpp_notmem_0063 f) (TEnvFresh.consFresh (nb078_alpha_dummy_005) (nb078_alpha_dummy_006 f) (nb078_wpp_notmem_0064) (nb078_wpp_notmem_0065 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0066) (nb078_wpp_notmem_0067 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))

noncomputable def nb078_wpp_refl_0001 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_033), (nb078_alpha_dummy_036 f)), ((nb078_alpha_dummy_032), (nb078_alpha_dummy_035 f)), ((nb078_alpha_dummy_031), (nb078_alpha_dummy_034 f)), ((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)), ((nb078_alpha_dummy_025), (nb078_alpha_dummy_027 f)), ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)), ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)), ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)), ((nb078_alpha_dummy_023), (nb078_alpha_dummy_024 f)), ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0001 x y f)

theorem nb078_wpp_notmem_0072 : (nb078_alpha_dummy_029) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_029, fv_syn_cnnc] using (nb078_compact_fv_empty_0006)

theorem nb078_wpp_notmem_0073 (f : Var) : (nb078_alpha_dummy_030 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_030, fv_syn_cnnc] using (nb078_compact_fv_empty_0007 f)

theorem nb078_wpp_notmem_0074 : (nb078_alpha_dummy_025) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_025, fv_syn_cnnc] using (nb078_compact_fv_empty_0008)

theorem nb078_wpp_notmem_0075 (f : Var) : (nb078_alpha_dummy_027 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_027, fv_syn_cnnc] using (nb078_compact_fv_empty_0009 f)

theorem nb078_wpp_notmem_0076 : (nb078_alpha_dummy_026) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_026, fv_syn_cnnc] using (nb078_compact_fv_empty_0010)

theorem nb078_wpp_notmem_0077 (f : Var) : (nb078_alpha_dummy_028 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_028, fv_syn_cnnc] using (nb078_compact_fv_empty_0011 f)

theorem nb078_wpp_notmem_0078 : (nb078_alpha_dummy_018) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_018, fv_syn_cnnc] using (nb078_compact_fv_empty_0012)

theorem nb078_wpp_notmem_0079 (f : Var) : (nb078_alpha_dummy_020 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_020, fv_syn_cnnc] using (nb078_compact_fv_empty_0013 f)

theorem nb078_wpp_notmem_0080 : (nb078_alpha_dummy_017) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_017, fv_syn_cnnc] using (nb078_compact_fv_empty_0014)

theorem nb078_wpp_notmem_0081 (f : Var) : (nb078_alpha_dummy_019 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_019, fv_syn_cnnc] using (nb078_compact_fv_empty_0015 f)

theorem nb078_wpp_notmem_0082 : (nb078_alpha_dummy_023) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_023, fv_syn_cnnc] using (nb078_compact_fv_empty_0016)

theorem nb078_wpp_notmem_0083 (f : Var) : (nb078_alpha_dummy_024 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_024, fv_syn_cnnc] using (nb078_compact_fv_empty_0017 f)

theorem nb078_wpp_notmem_0084 : (nb078_alpha_dummy_021) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_021, fv_syn_cnnc] using (nb078_compact_fv_empty_0018)

theorem nb078_wpp_notmem_0085 (f : Var) : (nb078_alpha_dummy_022 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_022, fv_syn_cnnc] using (nb078_compact_fv_empty_0019 f)

theorem nb078_wpp_notmem_0086 : (nb078_alpha_dummy_010) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_010, fv_syn_cnnc] using (nb078_compact_fv_empty_0020)

theorem nb078_wpp_notmem_0087 (f : Var) : (nb078_alpha_dummy_013 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_013, fv_syn_cnnc] using (nb078_compact_fv_empty_0021 f)

theorem nb078_wpp_notmem_0088 : (nb078_alpha_dummy_009) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_009, fv_syn_cnnc] using (nb078_compact_fv_empty_0022)

theorem nb078_wpp_notmem_0089 (f : Var) : (nb078_alpha_dummy_012 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_012, fv_syn_cnnc] using (nb078_compact_fv_empty_0023 f)

theorem nb078_wpp_notmem_0090 : (nb078_alpha_dummy_015) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_015, fv_syn_cnnc] using (nb078_compact_fv_empty_0024)

theorem nb078_wpp_notmem_0091 (f : Var) : (nb078_alpha_dummy_016 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_016, fv_syn_cnnc] using (nb078_compact_fv_empty_0025 f)

theorem nb078_wpp_notmem_0092 : (nb078_alpha_dummy_007) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_007, fv_syn_cnnc] using (nb078_compact_fv_empty_0026)

theorem nb078_wpp_notmem_0093 (f : Var) : (nb078_alpha_dummy_008 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_008, fv_syn_cnnc] using (nb078_compact_fv_empty_0027 f)

theorem nb078_wpp_notmem_0094 : (nb078_alpha_dummy_005) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_005, fv_syn_cnnc] using (nb078_compact_fv_empty_0028)

theorem nb078_wpp_notmem_0095 (f : Var) : (nb078_alpha_dummy_006 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_006, fv_syn_cnnc] using (nb078_compact_fv_empty_0029 f)

theorem nb078_wpp_notmem_0096 : (nb078_alpha_dummy_000) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_000, fv_syn_cnnc] using (nb078_compact_fv_empty_0030)

theorem nb078_wpp_notmem_0097 (f : Var) : f ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0031 f)

theorem nb078_wpp_notmem_0098 : (nb078_alpha_dummy_004) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_004, fv_syn_cnnc] using (nb078_compact_fv_empty_0032)

theorem nb078_wpp_notmem_0099 (y : Var) : y ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0033 y)

theorem nb078_wpp_notmem_0100 : (nb078_alpha_dummy_003) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_003, fv_syn_cnnc] using (nb078_compact_fv_empty_0034)

theorem nb078_wpp_notmem_0101 (x : Var) : x ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0035 x)

theorem nb078_compact_envfresh_0002 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)), ((nb078_alpha_dummy_025), (nb078_alpha_dummy_027 f)), ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)), ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)), ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)), ((nb078_alpha_dummy_023), (nb078_alpha_dummy_024 f)), ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_029) (nb078_alpha_dummy_030 f) (nb078_wpp_notmem_0072) (nb078_wpp_notmem_0073 f) (TEnvFresh.consFresh (nb078_alpha_dummy_025) (nb078_alpha_dummy_027 f) (nb078_wpp_notmem_0074) (nb078_wpp_notmem_0075 f) (TEnvFresh.consFresh (nb078_alpha_dummy_026) (nb078_alpha_dummy_028 f) (nb078_wpp_notmem_0076) (nb078_wpp_notmem_0077 f) (TEnvFresh.consFresh (nb078_alpha_dummy_018) (nb078_alpha_dummy_020 f) (nb078_wpp_notmem_0078) (nb078_wpp_notmem_0079 f) (TEnvFresh.consFresh (nb078_alpha_dummy_017) (nb078_alpha_dummy_019 f) (nb078_wpp_notmem_0080) (nb078_wpp_notmem_0081 f) (TEnvFresh.consFresh (nb078_alpha_dummy_023) (nb078_alpha_dummy_024 f) (nb078_wpp_notmem_0082) (nb078_wpp_notmem_0083 f) (TEnvFresh.consFresh (nb078_alpha_dummy_021) (nb078_alpha_dummy_022 f) (nb078_wpp_notmem_0084) (nb078_wpp_notmem_0085 f) (TEnvFresh.consFresh (nb078_alpha_dummy_010) (nb078_alpha_dummy_013 f) (nb078_wpp_notmem_0086) (nb078_wpp_notmem_0087 f) (TEnvFresh.consFresh (nb078_alpha_dummy_009) (nb078_alpha_dummy_012 f) (nb078_wpp_notmem_0088) (nb078_wpp_notmem_0089 f) (TEnvFresh.consFresh (nb078_alpha_dummy_015) (nb078_alpha_dummy_016 f) (nb078_wpp_notmem_0090) (nb078_wpp_notmem_0091 f) (TEnvFresh.consFresh (nb078_alpha_dummy_007) (nb078_alpha_dummy_008 f) (nb078_wpp_notmem_0092) (nb078_wpp_notmem_0093 f) (TEnvFresh.consFresh (nb078_alpha_dummy_005) (nb078_alpha_dummy_006 f) (nb078_wpp_notmem_0094) (nb078_wpp_notmem_0095 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0096) (nb078_wpp_notmem_0097 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))

noncomputable def nb078_wpp_refl_0002 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)), ((nb078_alpha_dummy_025), (nb078_alpha_dummy_027 f)), ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)), ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)), ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)), ((nb078_alpha_dummy_023), (nb078_alpha_dummy_024 f)), ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0002 x y f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
