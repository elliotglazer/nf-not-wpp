import NAR4C069C001Part001

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

theorem nb069_support_mem_0042 : (nb069_alpha_dummy_002) ∈ (((syn_cnin (Class.cv (nb069_alpha_dummy_002)) (Class.cv (nb069_alpha_dummy_003)))).fv ∪ ((syn_cnin (Class.cv (nb069_alpha_dummy_002)) (Class.cv (nb069_alpha_dummy_003)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0043 (x : Var) (y : Var) : x ∈ (((syn_cnin (Class.cv x) (Class.cv y))).fv ∪ ((syn_cnin (Class.cv x) (Class.cv y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0044 : (nb069_alpha_dummy_002) ∈ (((Class.cv (nb069_alpha_dummy_002))).fv ∪ ((Class.cv (nb069_alpha_dummy_003))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0045 (x : Var) (y : Var) : x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0046 : (nb069_alpha_dummy_003) ∈ (((syn_cnin (Class.cv (nb069_alpha_dummy_002)) (Class.cv (nb069_alpha_dummy_003)))).fv ∪ ((syn_cnin (Class.cv (nb069_alpha_dummy_002)) (Class.cv (nb069_alpha_dummy_003)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0047 (x : Var) (y : Var) : y ∈ (((syn_cnin (Class.cv x) (Class.cv y))).fv ∪ ((syn_cnin (Class.cv x) (Class.cv y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0048 : (nb069_alpha_dummy_003) ∈ (((Class.cv (nb069_alpha_dummy_002))).fv ∪ ((Class.cv (nb069_alpha_dummy_003))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0049 (x : Var) (y : Var) : y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_compact_fv_empty_0000 : (nb069_alpha_dummy_022) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0000 : (nb069_alpha_dummy_022) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_022, fv_syn_c1c] using (nb069_compact_fv_empty_0000)

theorem nb069_compact_fv_empty_0001 (a : Var) (b : Var) : (nb069_alpha_dummy_025 a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0001 (a : Var) (b : Var) : (nb069_alpha_dummy_025 a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_025, fv_syn_c1c] using (nb069_compact_fv_empty_0001 a b)

theorem nb069_compact_fv_empty_0002 : (nb069_alpha_dummy_021) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0002 : (nb069_alpha_dummy_021) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_021, fv_syn_c1c] using (nb069_compact_fv_empty_0002)

theorem nb069_compact_fv_empty_0003 (a : Var) (b : Var) : (nb069_alpha_dummy_024 a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0003 (a : Var) (b : Var) : (nb069_alpha_dummy_024 a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_024, fv_syn_c1c] using (nb069_compact_fv_empty_0003 a b)

theorem nb069_compact_fv_empty_0004 : (nb069_alpha_dummy_020) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0004 : (nb069_alpha_dummy_020) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_020, fv_syn_c1c] using (nb069_compact_fv_empty_0004)

theorem nb069_compact_fv_empty_0005 (a : Var) (b : Var) : (nb069_alpha_dummy_023 a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0005 (a : Var) (b : Var) : (nb069_alpha_dummy_023 a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_023, fv_syn_c1c] using (nb069_compact_fv_empty_0005 a b)

theorem nb069_compact_fv_empty_0006 : (nb069_alpha_dummy_018) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0006 : (nb069_alpha_dummy_018) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_018, fv_syn_c1c] using (nb069_compact_fv_empty_0006)

theorem nb069_compact_fv_empty_0007 (a : Var) (b : Var) : (nb069_alpha_dummy_019 a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0007 (a : Var) (b : Var) : (nb069_alpha_dummy_019 a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_019, fv_syn_c1c] using (nb069_compact_fv_empty_0007 a b)

theorem nb069_compact_fv_empty_0008 : (nb069_alpha_dummy_014) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0008 : (nb069_alpha_dummy_014) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_014, fv_syn_c1c] using (nb069_compact_fv_empty_0008)

theorem nb069_compact_fv_empty_0009 (a : Var) (b : Var) : (nb069_alpha_dummy_016 a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0009 (a : Var) (b : Var) : (nb069_alpha_dummy_016 a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_016, fv_syn_c1c] using (nb069_compact_fv_empty_0009 a b)

theorem nb069_compact_fv_empty_0010 : (nb069_alpha_dummy_015) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0010 : (nb069_alpha_dummy_015) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_015, fv_syn_c1c] using (nb069_compact_fv_empty_0010)

theorem nb069_compact_fv_empty_0011 (a : Var) (b : Var) : (nb069_alpha_dummy_017 a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0011 (a : Var) (b : Var) : (nb069_alpha_dummy_017 a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_017, fv_syn_c1c] using (nb069_compact_fv_empty_0011 a b)

theorem nb069_compact_fv_empty_0012 : (nb069_alpha_dummy_007) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0012 : (nb069_alpha_dummy_007) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_007, fv_syn_c1c] using (nb069_compact_fv_empty_0012)

theorem nb069_compact_fv_empty_0013 (a : Var) (b : Var) : (nb069_alpha_dummy_009 a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0013 (a : Var) (b : Var) : (nb069_alpha_dummy_009 a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_009, fv_syn_c1c] using (nb069_compact_fv_empty_0013 a b)

theorem nb069_compact_fv_empty_0014 : (nb069_alpha_dummy_006) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0014 : (nb069_alpha_dummy_006) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_006, fv_syn_c1c] using (nb069_compact_fv_empty_0014)

theorem nb069_compact_fv_empty_0015 (a : Var) (b : Var) : (nb069_alpha_dummy_008 a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0015 (a : Var) (b : Var) : (nb069_alpha_dummy_008 a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_008, fv_syn_c1c] using (nb069_compact_fv_empty_0015 a b)

theorem nb069_compact_fv_empty_0016 : (nb069_alpha_dummy_012) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0016 : (nb069_alpha_dummy_012) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_012, fv_syn_c1c] using (nb069_compact_fv_empty_0016)

theorem nb069_compact_fv_empty_0017 (a : Var) (b : Var) : (nb069_alpha_dummy_013 a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0017 (a : Var) (b : Var) : (nb069_alpha_dummy_013 a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_013, fv_syn_c1c] using (nb069_compact_fv_empty_0017 a b)

theorem nb069_compact_fv_empty_0018 : (nb069_alpha_dummy_010) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0018 : (nb069_alpha_dummy_010) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_010, fv_syn_c1c] using (nb069_compact_fv_empty_0018)

theorem nb069_compact_fv_empty_0019 (a : Var) (b : Var) : (nb069_alpha_dummy_011 a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0019 (a : Var) (b : Var) : (nb069_alpha_dummy_011 a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_011, fv_syn_c1c] using (nb069_compact_fv_empty_0019 a b)

theorem nb069_compact_fv_empty_0020 : (nb069_alpha_dummy_001) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0020 : (nb069_alpha_dummy_001) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_001, fv_syn_c1c] using (nb069_compact_fv_empty_0020)

theorem nb069_compact_fv_empty_0021 (b : Var) : b ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0021 (b : Var) : b ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb069_compact_fv_empty_0021 b)

theorem nb069_compact_fv_empty_0022 : (nb069_alpha_dummy_000) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0022 : (nb069_alpha_dummy_000) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_000, fv_syn_c1c] using (nb069_compact_fv_empty_0022)

theorem nb069_compact_fv_empty_0023 (a : Var) : a ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0023 (a : Var) : a ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb069_compact_fv_empty_0023 a)

theorem nb069_compact_fv_empty_0024 : (nb069_alpha_dummy_004) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0024 : (nb069_alpha_dummy_004) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_004, fv_syn_c1c] using (nb069_compact_fv_empty_0024)

theorem nb069_compact_fv_empty_0025 (x : Var) (y : Var) (a : Var) (b : Var) : (nb069_alpha_dummy_005 x y a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0025 (x : Var) (y : Var) (a : Var) (b : Var) : (nb069_alpha_dummy_005 x y a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_005, fv_syn_c1c] using (nb069_compact_fv_empty_0025 x y a b)

theorem nb069_compact_envfresh_0000 (x : Var) (y : Var) (a : Var) (b : Var) : TEnvFresh [((nb069_alpha_dummy_022), (nb069_alpha_dummy_025 a b)), ((nb069_alpha_dummy_021), (nb069_alpha_dummy_024 a b)), ((nb069_alpha_dummy_020), (nb069_alpha_dummy_023 a b)), ((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)), ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)), ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)), ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)), ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)), ((nb069_alpha_dummy_012), (nb069_alpha_dummy_013 a b)), ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)), ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a), ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb069_alpha_dummy_022) (nb069_alpha_dummy_025 a b) (nb069_wpp_notmem_0000) (nb069_wpp_notmem_0001 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_021) (nb069_alpha_dummy_024 a b) (nb069_wpp_notmem_0002) (nb069_wpp_notmem_0003 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_020) (nb069_alpha_dummy_023 a b) (nb069_wpp_notmem_0004) (nb069_wpp_notmem_0005 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_018) (nb069_alpha_dummy_019 a b) (nb069_wpp_notmem_0006) (nb069_wpp_notmem_0007 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_014) (nb069_alpha_dummy_016 a b) (nb069_wpp_notmem_0008) (nb069_wpp_notmem_0009 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_015) (nb069_alpha_dummy_017 a b) (nb069_wpp_notmem_0010) (nb069_wpp_notmem_0011 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_007) (nb069_alpha_dummy_009 a b) (nb069_wpp_notmem_0012) (nb069_wpp_notmem_0013 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_006) (nb069_alpha_dummy_008 a b) (nb069_wpp_notmem_0014) (nb069_wpp_notmem_0015 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_012) (nb069_alpha_dummy_013 a b) (nb069_wpp_notmem_0016) (nb069_wpp_notmem_0017 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_010) (nb069_alpha_dummy_011 a b) (nb069_wpp_notmem_0018) (nb069_wpp_notmem_0019 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_001) b (nb069_wpp_notmem_0020) (nb069_wpp_notmem_0021 b) (TEnvFresh.consFresh (nb069_alpha_dummy_000) a (nb069_wpp_notmem_0022) (nb069_wpp_notmem_0023 a) (TEnvFresh.consFresh (nb069_alpha_dummy_004) (nb069_alpha_dummy_005 x y a b) (nb069_wpp_notmem_0024) (nb069_wpp_notmem_0025 x y a b) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))

noncomputable def nb069_wpp_refl_0000 (x : Var) (y : Var) (a : Var) (b : Var) : TReflOn [((nb069_alpha_dummy_022), (nb069_alpha_dummy_025 a b)), ((nb069_alpha_dummy_021), (nb069_alpha_dummy_024 a b)), ((nb069_alpha_dummy_020), (nb069_alpha_dummy_023 a b)), ((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)), ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)), ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)), ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)), ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)), ((nb069_alpha_dummy_012), (nb069_alpha_dummy_013 a b)), ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)), ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a), ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb069_compact_envfresh_0000 x y a b)

theorem nb069_wpp_notmem_0026 : (nb069_alpha_dummy_022) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_022, fv_syn_c0] using (nb069_compact_fv_empty_0000)

theorem nb069_wpp_notmem_0027 (a : Var) (b : Var) : (nb069_alpha_dummy_025 a b) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_025, fv_syn_c0] using (nb069_compact_fv_empty_0001 a b)

theorem nb069_wpp_notmem_0028 : (nb069_alpha_dummy_021) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_021, fv_syn_c0] using (nb069_compact_fv_empty_0002)

theorem nb069_wpp_notmem_0029 (a : Var) (b : Var) : (nb069_alpha_dummy_024 a b) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_024, fv_syn_c0] using (nb069_compact_fv_empty_0003 a b)

theorem nb069_wpp_notmem_0030 : (nb069_alpha_dummy_020) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_020, fv_syn_c0] using (nb069_compact_fv_empty_0004)

theorem nb069_wpp_notmem_0031 (a : Var) (b : Var) : (nb069_alpha_dummy_023 a b) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_023, fv_syn_c0] using (nb069_compact_fv_empty_0005 a b)

theorem nb069_wpp_notmem_0032 : (nb069_alpha_dummy_018) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_018, fv_syn_c0] using (nb069_compact_fv_empty_0006)

theorem nb069_wpp_notmem_0033 (a : Var) (b : Var) : (nb069_alpha_dummy_019 a b) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_019, fv_syn_c0] using (nb069_compact_fv_empty_0007 a b)

theorem nb069_wpp_notmem_0034 : (nb069_alpha_dummy_014) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_014, fv_syn_c0] using (nb069_compact_fv_empty_0008)

theorem nb069_wpp_notmem_0035 (a : Var) (b : Var) : (nb069_alpha_dummy_016 a b) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_016, fv_syn_c0] using (nb069_compact_fv_empty_0009 a b)

theorem nb069_wpp_notmem_0036 : (nb069_alpha_dummy_015) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_015, fv_syn_c0] using (nb069_compact_fv_empty_0010)

theorem nb069_wpp_notmem_0037 (a : Var) (b : Var) : (nb069_alpha_dummy_017 a b) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_017, fv_syn_c0] using (nb069_compact_fv_empty_0011 a b)

theorem nb069_wpp_notmem_0038 : (nb069_alpha_dummy_007) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_007, fv_syn_c0] using (nb069_compact_fv_empty_0012)

theorem nb069_wpp_notmem_0039 (a : Var) (b : Var) : (nb069_alpha_dummy_009 a b) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_009, fv_syn_c0] using (nb069_compact_fv_empty_0013 a b)

theorem nb069_wpp_notmem_0040 : (nb069_alpha_dummy_006) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_006, fv_syn_c0] using (nb069_compact_fv_empty_0014)

theorem nb069_wpp_notmem_0041 (a : Var) (b : Var) : (nb069_alpha_dummy_008 a b) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_008, fv_syn_c0] using (nb069_compact_fv_empty_0015 a b)

theorem nb069_wpp_notmem_0042 : (nb069_alpha_dummy_012) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_012, fv_syn_c0] using (nb069_compact_fv_empty_0016)

theorem nb069_wpp_notmem_0043 (a : Var) (b : Var) : (nb069_alpha_dummy_013 a b) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_013, fv_syn_c0] using (nb069_compact_fv_empty_0017 a b)

theorem nb069_wpp_notmem_0044 : (nb069_alpha_dummy_010) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_010, fv_syn_c0] using (nb069_compact_fv_empty_0018)

theorem nb069_wpp_notmem_0045 (a : Var) (b : Var) : (nb069_alpha_dummy_011 a b) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_011, fv_syn_c0] using (nb069_compact_fv_empty_0019 a b)

theorem nb069_wpp_notmem_0046 : (nb069_alpha_dummy_001) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_001, fv_syn_c0] using (nb069_compact_fv_empty_0020)

theorem nb069_wpp_notmem_0047 (b : Var) : b ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb069_compact_fv_empty_0021 b)

theorem nb069_wpp_notmem_0048 : (nb069_alpha_dummy_000) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_000, fv_syn_c0] using (nb069_compact_fv_empty_0022)

theorem nb069_wpp_notmem_0049 (a : Var) : a ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb069_compact_fv_empty_0023 a)

theorem nb069_wpp_notmem_0050 : (nb069_alpha_dummy_004) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_004, fv_syn_c0] using (nb069_compact_fv_empty_0024)

theorem nb069_wpp_notmem_0051 (x : Var) (y : Var) (a : Var) (b : Var) : (nb069_alpha_dummy_005 x y a b) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_005, fv_syn_c0] using (nb069_compact_fv_empty_0025 x y a b)

theorem nb069_compact_envfresh_0001 (x : Var) (y : Var) (a : Var) (b : Var) : TEnvFresh [((nb069_alpha_dummy_022), (nb069_alpha_dummy_025 a b)), ((nb069_alpha_dummy_021), (nb069_alpha_dummy_024 a b)), ((nb069_alpha_dummy_020), (nb069_alpha_dummy_023 a b)), ((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)), ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)), ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)), ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)), ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)), ((nb069_alpha_dummy_012), (nb069_alpha_dummy_013 a b)), ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)), ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a), ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb069_alpha_dummy_022) (nb069_alpha_dummy_025 a b) (nb069_wpp_notmem_0026) (nb069_wpp_notmem_0027 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_021) (nb069_alpha_dummy_024 a b) (nb069_wpp_notmem_0028) (nb069_wpp_notmem_0029 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_020) (nb069_alpha_dummy_023 a b) (nb069_wpp_notmem_0030) (nb069_wpp_notmem_0031 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_018) (nb069_alpha_dummy_019 a b) (nb069_wpp_notmem_0032) (nb069_wpp_notmem_0033 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_014) (nb069_alpha_dummy_016 a b) (nb069_wpp_notmem_0034) (nb069_wpp_notmem_0035 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_015) (nb069_alpha_dummy_017 a b) (nb069_wpp_notmem_0036) (nb069_wpp_notmem_0037 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_007) (nb069_alpha_dummy_009 a b) (nb069_wpp_notmem_0038) (nb069_wpp_notmem_0039 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_006) (nb069_alpha_dummy_008 a b) (nb069_wpp_notmem_0040) (nb069_wpp_notmem_0041 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_012) (nb069_alpha_dummy_013 a b) (nb069_wpp_notmem_0042) (nb069_wpp_notmem_0043 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_010) (nb069_alpha_dummy_011 a b) (nb069_wpp_notmem_0044) (nb069_wpp_notmem_0045 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_001) b (nb069_wpp_notmem_0046) (nb069_wpp_notmem_0047 b) (TEnvFresh.consFresh (nb069_alpha_dummy_000) a (nb069_wpp_notmem_0048) (nb069_wpp_notmem_0049 a) (TEnvFresh.consFresh (nb069_alpha_dummy_004) (nb069_alpha_dummy_005 x y a b) (nb069_wpp_notmem_0050) (nb069_wpp_notmem_0051 x y a b) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))

noncomputable def nb069_wpp_refl_0001 (x : Var) (y : Var) (a : Var) (b : Var) : TReflOn [((nb069_alpha_dummy_022), (nb069_alpha_dummy_025 a b)), ((nb069_alpha_dummy_021), (nb069_alpha_dummy_024 a b)), ((nb069_alpha_dummy_020), (nb069_alpha_dummy_023 a b)), ((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)), ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)), ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)), ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)), ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)), ((nb069_alpha_dummy_012), (nb069_alpha_dummy_013 a b)), ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)), ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a), ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb069_compact_envfresh_0001 x y a b)

noncomputable def nb069_split_alpha_0000 (x : Var) (y : Var) (a : Var) (b : Var) : TAlphaWff [((nb069_alpha_dummy_022), (nb069_alpha_dummy_025 a b)), ((nb069_alpha_dummy_021), (nb069_alpha_dummy_024 a b)), ((nb069_alpha_dummy_020), (nb069_alpha_dummy_023 a b)), ((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)), ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)), ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)), ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)), ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)), ((nb069_alpha_dummy_012), (nb069_alpha_dummy_013 a b)), ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)), ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a), ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb069_alpha_dummy_021)) (Class.cv (nb069_alpha_dummy_022))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb069_alpha_dummy_020)) (syn_cun (Class.cv (nb069_alpha_dummy_021)) (Class.cv (nb069_alpha_dummy_022)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb069_alpha_dummy_024 a b)) (Class.cv (nb069_alpha_dummy_025 a b))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb069_alpha_dummy_023 a b)) (syn_cun (Class.cv (nb069_alpha_dummy_024 a b)) (Class.cv (nb069_alpha_dummy_025 a b)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0019 a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0017 a b) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0023 a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0021 a b) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0019 a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0017 a b) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0023 a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0021 a b) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb069_alpha_dummy_022), (nb069_alpha_dummy_025 a b)), ((nb069_alpha_dummy_021), (nb069_alpha_dummy_024 a b)), ((nb069_alpha_dummy_020), (nb069_alpha_dummy_023 a b)), ((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)), ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)), ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)), ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)), ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)), ((nb069_alpha_dummy_012), (nb069_alpha_dummy_013 a b)), ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)), ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a), ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))] (syn_c0) (nb069_wpp_refl_0001 x y a b))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0027 a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0025 a b) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0027 a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0025 a b) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0031 a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0029 a b) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0031 a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0029 a b) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb069_wpp_notmem_0052 : (nb069_alpha_dummy_018) ∉ ((syn_cnnc)).fv := by
  simpa only [nb069_alpha_dummy_018, fv_syn_cnnc] using (nb069_compact_fv_empty_0006)

theorem nb069_wpp_notmem_0053 (a : Var) (b : Var) : (nb069_alpha_dummy_019 a b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb069_alpha_dummy_019, fv_syn_cnnc] using (nb069_compact_fv_empty_0007 a b)

theorem nb069_wpp_notmem_0054 : (nb069_alpha_dummy_014) ∉ ((syn_cnnc)).fv := by
  simpa only [nb069_alpha_dummy_014, fv_syn_cnnc] using (nb069_compact_fv_empty_0008)

theorem nb069_wpp_notmem_0055 (a : Var) (b : Var) : (nb069_alpha_dummy_016 a b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb069_alpha_dummy_016, fv_syn_cnnc] using (nb069_compact_fv_empty_0009 a b)

theorem nb069_wpp_notmem_0056 : (nb069_alpha_dummy_015) ∉ ((syn_cnnc)).fv := by
  simpa only [nb069_alpha_dummy_015, fv_syn_cnnc] using (nb069_compact_fv_empty_0010)

theorem nb069_wpp_notmem_0057 (a : Var) (b : Var) : (nb069_alpha_dummy_017 a b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb069_alpha_dummy_017, fv_syn_cnnc] using (nb069_compact_fv_empty_0011 a b)

theorem nb069_wpp_notmem_0058 : (nb069_alpha_dummy_007) ∉ ((syn_cnnc)).fv := by
  simpa only [nb069_alpha_dummy_007, fv_syn_cnnc] using (nb069_compact_fv_empty_0012)

theorem nb069_wpp_notmem_0059 (a : Var) (b : Var) : (nb069_alpha_dummy_009 a b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb069_alpha_dummy_009, fv_syn_cnnc] using (nb069_compact_fv_empty_0013 a b)

theorem nb069_wpp_notmem_0060 : (nb069_alpha_dummy_006) ∉ ((syn_cnnc)).fv := by
  simpa only [nb069_alpha_dummy_006, fv_syn_cnnc] using (nb069_compact_fv_empty_0014)

theorem nb069_wpp_notmem_0061 (a : Var) (b : Var) : (nb069_alpha_dummy_008 a b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb069_alpha_dummy_008, fv_syn_cnnc] using (nb069_compact_fv_empty_0015 a b)

theorem nb069_wpp_notmem_0062 : (nb069_alpha_dummy_012) ∉ ((syn_cnnc)).fv := by
  simpa only [nb069_alpha_dummy_012, fv_syn_cnnc] using (nb069_compact_fv_empty_0016)

theorem nb069_wpp_notmem_0063 (a : Var) (b : Var) : (nb069_alpha_dummy_013 a b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb069_alpha_dummy_013, fv_syn_cnnc] using (nb069_compact_fv_empty_0017 a b)

theorem nb069_wpp_notmem_0064 : (nb069_alpha_dummy_010) ∉ ((syn_cnnc)).fv := by
  simpa only [nb069_alpha_dummy_010, fv_syn_cnnc] using (nb069_compact_fv_empty_0018)

theorem nb069_wpp_notmem_0065 (a : Var) (b : Var) : (nb069_alpha_dummy_011 a b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb069_alpha_dummy_011, fv_syn_cnnc] using (nb069_compact_fv_empty_0019 a b)

theorem nb069_wpp_notmem_0066 : (nb069_alpha_dummy_001) ∉ ((syn_cnnc)).fv := by
  simpa only [nb069_alpha_dummy_001, fv_syn_cnnc] using (nb069_compact_fv_empty_0020)

theorem nb069_wpp_notmem_0067 (b : Var) : b ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb069_compact_fv_empty_0021 b)

theorem nb069_wpp_notmem_0068 : (nb069_alpha_dummy_000) ∉ ((syn_cnnc)).fv := by
  simpa only [nb069_alpha_dummy_000, fv_syn_cnnc] using (nb069_compact_fv_empty_0022)

theorem nb069_wpp_notmem_0069 (a : Var) : a ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb069_compact_fv_empty_0023 a)

theorem nb069_wpp_notmem_0070 : (nb069_alpha_dummy_004) ∉ ((syn_cnnc)).fv := by
  simpa only [nb069_alpha_dummy_004, fv_syn_cnnc] using (nb069_compact_fv_empty_0024)

theorem nb069_wpp_notmem_0071 (x : Var) (y : Var) (a : Var) (b : Var) : (nb069_alpha_dummy_005 x y a b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb069_alpha_dummy_005, fv_syn_cnnc] using (nb069_compact_fv_empty_0025 x y a b)

theorem nb069_compact_envfresh_0002 (x : Var) (y : Var) (a : Var) (b : Var) : TEnvFresh [((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)), ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)), ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)), ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)), ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)), ((nb069_alpha_dummy_012), (nb069_alpha_dummy_013 a b)), ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)), ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a), ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb069_alpha_dummy_018) (nb069_alpha_dummy_019 a b) (nb069_wpp_notmem_0052) (nb069_wpp_notmem_0053 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_014) (nb069_alpha_dummy_016 a b) (nb069_wpp_notmem_0054) (nb069_wpp_notmem_0055 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_015) (nb069_alpha_dummy_017 a b) (nb069_wpp_notmem_0056) (nb069_wpp_notmem_0057 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_007) (nb069_alpha_dummy_009 a b) (nb069_wpp_notmem_0058) (nb069_wpp_notmem_0059 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_006) (nb069_alpha_dummy_008 a b) (nb069_wpp_notmem_0060) (nb069_wpp_notmem_0061 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_012) (nb069_alpha_dummy_013 a b) (nb069_wpp_notmem_0062) (nb069_wpp_notmem_0063 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_010) (nb069_alpha_dummy_011 a b) (nb069_wpp_notmem_0064) (nb069_wpp_notmem_0065 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_001) b (nb069_wpp_notmem_0066) (nb069_wpp_notmem_0067 b) (TEnvFresh.consFresh (nb069_alpha_dummy_000) a (nb069_wpp_notmem_0068) (nb069_wpp_notmem_0069 a) (TEnvFresh.consFresh (nb069_alpha_dummy_004) (nb069_alpha_dummy_005 x y a b) (nb069_wpp_notmem_0070) (nb069_wpp_notmem_0071 x y a b) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))

noncomputable def nb069_wpp_refl_0002 (x : Var) (y : Var) (a : Var) (b : Var) : TReflOn [((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)), ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)), ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)), ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)), ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)), ((nb069_alpha_dummy_012), (nb069_alpha_dummy_013 a b)), ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)), ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a), ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb069_compact_envfresh_0002 x y a b)

noncomputable def nb069_split_alpha_0001 (x : Var) (y : Var) (a : Var) (b : Var) (dv_a_b : a ≠ b) : TAlphaWff [((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)), ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)), ((nb069_alpha_dummy_012), (nb069_alpha_dummy_013 a b)), ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)), ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a), ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))] (Wff.imp (Wff.classMem (Class.cv (nb069_alpha_dummy_007)) (Class.cv (nb069_alpha_dummy_000))) (Wff.neg (Wff.classEq (Class.cv (nb069_alpha_dummy_006)) (syn_cphi (Class.cv (nb069_alpha_dummy_007)))))) (Wff.imp (Wff.classMem (Class.cv (nb069_alpha_dummy_009 a b)) (Class.cv a)) (Wff.neg (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b)) (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0004) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0006 a b) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0004) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0006 a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0008) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0009 a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0005) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0007 a b) 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_b (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb069_alpha_dummy_000))).fv ∪ ((Class.cv (nb069_alpha_dummy_001))).fv) (by decide)) (freshVar_injective (((Class.cv a)).fv ∪ ((Class.cv b)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0010) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0011 a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0010) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0011 a b) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb069_alpha_dummy_007))).fv) (by decide)) (freshVar_injective (((Class.cv (nb069_alpha_dummy_009 a b))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0014) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0015 a b) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0015 a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0013 a b) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb069_alpha_dummy_022), (nb069_alpha_dummy_025 a b)), ((nb069_alpha_dummy_021), (nb069_alpha_dummy_024 a b)), ((nb069_alpha_dummy_020), (nb069_alpha_dummy_023 a b)), ((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)), ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)), ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)), ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)), ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)), ((nb069_alpha_dummy_012), (nb069_alpha_dummy_013 a b)), ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)), ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a), ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))] (syn_c1c) (nb069_wpp_refl_0000 x y a b))) (TAlphaWff.neg (TAlphaWff.neg (nb069_split_alpha_0000 x y a b)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0013 a b) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)), ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)), ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)), ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)), ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)), ((nb069_alpha_dummy_012), (nb069_alpha_dummy_013 a b)), ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)), ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a), ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))] (syn_cnnc) (nb069_wpp_refl_0002 x y a b))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0013 a b) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0013 a b) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)), ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)), ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)), ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)), ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)), ((nb069_alpha_dummy_012), (nb069_alpha_dummy_013 a b)), ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)), ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a), ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))] (syn_cnnc) (nb069_wpp_refl_0002 x y a b))))))))))))))))))))

theorem nb069_compact_fv_empty_0026 : (nb069_alpha_dummy_040) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0072 : (nb069_alpha_dummy_040) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_040, fv_syn_c1c] using (nb069_compact_fv_empty_0026)

theorem nb069_compact_fv_empty_0027 (a : Var) (b : Var) : (nb069_alpha_dummy_041 a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0073 (a : Var) (b : Var) : (nb069_alpha_dummy_041 a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_041, fv_syn_c1c] using (nb069_compact_fv_empty_0027 a b)

theorem nb069_compact_fv_empty_0028 : (nb069_alpha_dummy_038) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0074 : (nb069_alpha_dummy_038) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_038, fv_syn_c1c] using (nb069_compact_fv_empty_0028)

theorem nb069_compact_fv_empty_0029 (a : Var) (b : Var) : (nb069_alpha_dummy_039 a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0075 (a : Var) (b : Var) : (nb069_alpha_dummy_039 a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_039, fv_syn_c1c] using (nb069_compact_fv_empty_0029 a b)

theorem nb069_compact_fv_empty_0030 : (nb069_alpha_dummy_036) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0076 : (nb069_alpha_dummy_036) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_036, fv_syn_c1c] using (nb069_compact_fv_empty_0030)

theorem nb069_compact_fv_empty_0031 (a : Var) (b : Var) : (nb069_alpha_dummy_037 a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb069_wpp_notmem_0077 (a : Var) (b : Var) : (nb069_alpha_dummy_037 a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb069_alpha_dummy_037, fv_syn_c1c] using (nb069_compact_fv_empty_0031 a b)

theorem nb069_compact_envfresh_0003 (x : Var) (y : Var) (a : Var) (b : Var) : TEnvFresh [((nb069_alpha_dummy_022), (nb069_alpha_dummy_025 a b)), ((nb069_alpha_dummy_021), (nb069_alpha_dummy_024 a b)), ((nb069_alpha_dummy_020), (nb069_alpha_dummy_023 a b)), ((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)), ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)), ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)), ((nb069_alpha_dummy_040), (nb069_alpha_dummy_041 a b)), ((nb069_alpha_dummy_038), (nb069_alpha_dummy_039 a b)), ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)), ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)), ((nb069_alpha_dummy_036), (nb069_alpha_dummy_037 a b)), ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)), ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a), ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb069_alpha_dummy_022) (nb069_alpha_dummy_025 a b) (nb069_wpp_notmem_0000) (nb069_wpp_notmem_0001 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_021) (nb069_alpha_dummy_024 a b) (nb069_wpp_notmem_0002) (nb069_wpp_notmem_0003 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_020) (nb069_alpha_dummy_023 a b) (nb069_wpp_notmem_0004) (nb069_wpp_notmem_0005 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_018) (nb069_alpha_dummy_019 a b) (nb069_wpp_notmem_0006) (nb069_wpp_notmem_0007 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_014) (nb069_alpha_dummy_016 a b) (nb069_wpp_notmem_0008) (nb069_wpp_notmem_0009 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_015) (nb069_alpha_dummy_017 a b) (nb069_wpp_notmem_0010) (nb069_wpp_notmem_0011 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_040) (nb069_alpha_dummy_041 a b) (nb069_wpp_notmem_0072) (nb069_wpp_notmem_0073 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_038) (nb069_alpha_dummy_039 a b) (nb069_wpp_notmem_0074) (nb069_wpp_notmem_0075 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_007) (nb069_alpha_dummy_009 a b) (nb069_wpp_notmem_0012) (nb069_wpp_notmem_0013 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_006) (nb069_alpha_dummy_008 a b) (nb069_wpp_notmem_0014) (nb069_wpp_notmem_0015 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_036) (nb069_alpha_dummy_037 a b) (nb069_wpp_notmem_0076) (nb069_wpp_notmem_0077 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_010) (nb069_alpha_dummy_011 a b) (nb069_wpp_notmem_0018) (nb069_wpp_notmem_0019 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_001) b (nb069_wpp_notmem_0020) (nb069_wpp_notmem_0021 b) (TEnvFresh.consFresh (nb069_alpha_dummy_000) a (nb069_wpp_notmem_0022) (nb069_wpp_notmem_0023 a) (TEnvFresh.consFresh (nb069_alpha_dummy_004) (nb069_alpha_dummy_005 x y a b) (nb069_wpp_notmem_0024) (nb069_wpp_notmem_0025 x y a b) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb069_wpp_refl_0003 (x : Var) (y : Var) (a : Var) (b : Var) : TReflOn [((nb069_alpha_dummy_022), (nb069_alpha_dummy_025 a b)), ((nb069_alpha_dummy_021), (nb069_alpha_dummy_024 a b)), ((nb069_alpha_dummy_020), (nb069_alpha_dummy_023 a b)), ((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)), ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)), ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)), ((nb069_alpha_dummy_040), (nb069_alpha_dummy_041 a b)), ((nb069_alpha_dummy_038), (nb069_alpha_dummy_039 a b)), ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)), ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)), ((nb069_alpha_dummy_036), (nb069_alpha_dummy_037 a b)), ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)), ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a), ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb069_compact_envfresh_0003 x y a b)

theorem nb069_wpp_notmem_0078 : (nb069_alpha_dummy_040) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_040, fv_syn_c0] using (nb069_compact_fv_empty_0026)

theorem nb069_wpp_notmem_0079 (a : Var) (b : Var) : (nb069_alpha_dummy_041 a b) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_041, fv_syn_c0] using (nb069_compact_fv_empty_0027 a b)

theorem nb069_wpp_notmem_0080 : (nb069_alpha_dummy_038) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_038, fv_syn_c0] using (nb069_compact_fv_empty_0028)

theorem nb069_wpp_notmem_0081 (a : Var) (b : Var) : (nb069_alpha_dummy_039 a b) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_039, fv_syn_c0] using (nb069_compact_fv_empty_0029 a b)

theorem nb069_wpp_notmem_0082 : (nb069_alpha_dummy_036) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_036, fv_syn_c0] using (nb069_compact_fv_empty_0030)

theorem nb069_wpp_notmem_0083 (a : Var) (b : Var) : (nb069_alpha_dummy_037 a b) ∉ ((syn_c0)).fv := by
  simpa only [nb069_alpha_dummy_037, fv_syn_c0] using (nb069_compact_fv_empty_0031 a b)

theorem nb069_compact_envfresh_0004 (x : Var) (y : Var) (a : Var) (b : Var) : TEnvFresh [((nb069_alpha_dummy_022), (nb069_alpha_dummy_025 a b)), ((nb069_alpha_dummy_021), (nb069_alpha_dummy_024 a b)), ((nb069_alpha_dummy_020), (nb069_alpha_dummy_023 a b)), ((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)), ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)), ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)), ((nb069_alpha_dummy_040), (nb069_alpha_dummy_041 a b)), ((nb069_alpha_dummy_038), (nb069_alpha_dummy_039 a b)), ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)), ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)), ((nb069_alpha_dummy_036), (nb069_alpha_dummy_037 a b)), ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)), ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a), ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb069_alpha_dummy_022) (nb069_alpha_dummy_025 a b) (nb069_wpp_notmem_0026) (nb069_wpp_notmem_0027 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_021) (nb069_alpha_dummy_024 a b) (nb069_wpp_notmem_0028) (nb069_wpp_notmem_0029 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_020) (nb069_alpha_dummy_023 a b) (nb069_wpp_notmem_0030) (nb069_wpp_notmem_0031 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_018) (nb069_alpha_dummy_019 a b) (nb069_wpp_notmem_0032) (nb069_wpp_notmem_0033 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_014) (nb069_alpha_dummy_016 a b) (nb069_wpp_notmem_0034) (nb069_wpp_notmem_0035 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_015) (nb069_alpha_dummy_017 a b) (nb069_wpp_notmem_0036) (nb069_wpp_notmem_0037 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_040) (nb069_alpha_dummy_041 a b) (nb069_wpp_notmem_0078) (nb069_wpp_notmem_0079 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_038) (nb069_alpha_dummy_039 a b) (nb069_wpp_notmem_0080) (nb069_wpp_notmem_0081 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_007) (nb069_alpha_dummy_009 a b) (nb069_wpp_notmem_0038) (nb069_wpp_notmem_0039 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_006) (nb069_alpha_dummy_008 a b) (nb069_wpp_notmem_0040) (nb069_wpp_notmem_0041 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_036) (nb069_alpha_dummy_037 a b) (nb069_wpp_notmem_0082) (nb069_wpp_notmem_0083 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_010) (nb069_alpha_dummy_011 a b) (nb069_wpp_notmem_0044) (nb069_wpp_notmem_0045 a b) (TEnvFresh.consFresh (nb069_alpha_dummy_001) b (nb069_wpp_notmem_0046) (nb069_wpp_notmem_0047 b) (TEnvFresh.consFresh (nb069_alpha_dummy_000) a (nb069_wpp_notmem_0048) (nb069_wpp_notmem_0049 a) (TEnvFresh.consFresh (nb069_alpha_dummy_004) (nb069_alpha_dummy_005 x y a b) (nb069_wpp_notmem_0050) (nb069_wpp_notmem_0051 x y a b) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))

noncomputable def nb069_wpp_refl_0004 (x : Var) (y : Var) (a : Var) (b : Var) : TReflOn [((nb069_alpha_dummy_022), (nb069_alpha_dummy_025 a b)), ((nb069_alpha_dummy_021), (nb069_alpha_dummy_024 a b)), ((nb069_alpha_dummy_020), (nb069_alpha_dummy_023 a b)), ((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)), ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)), ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)), ((nb069_alpha_dummy_040), (nb069_alpha_dummy_041 a b)), ((nb069_alpha_dummy_038), (nb069_alpha_dummy_039 a b)), ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)), ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)), ((nb069_alpha_dummy_036), (nb069_alpha_dummy_037 a b)), ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)), ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a), ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb069_compact_envfresh_0004 x y a b)

noncomputable def nb069_split_alpha_0002 (x : Var) (y : Var) (a : Var) (b : Var) : TAlphaWff [((nb069_alpha_dummy_022), (nb069_alpha_dummy_025 a b)), ((nb069_alpha_dummy_021), (nb069_alpha_dummy_024 a b)), ((nb069_alpha_dummy_020), (nb069_alpha_dummy_023 a b)), ((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)), ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)), ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)), ((nb069_alpha_dummy_040), (nb069_alpha_dummy_041 a b)), ((nb069_alpha_dummy_038), (nb069_alpha_dummy_039 a b)), ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)), ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)), ((nb069_alpha_dummy_036), (nb069_alpha_dummy_037 a b)), ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)), ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a), ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb069_alpha_dummy_021)) (Class.cv (nb069_alpha_dummy_022))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb069_alpha_dummy_020)) (syn_cun (Class.cv (nb069_alpha_dummy_021)) (Class.cv (nb069_alpha_dummy_022)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb069_alpha_dummy_024 a b)) (Class.cv (nb069_alpha_dummy_025 a b))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb069_alpha_dummy_023 a b)) (syn_cun (Class.cv (nb069_alpha_dummy_024 a b)) (Class.cv (nb069_alpha_dummy_025 a b)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0019 a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0017 a b) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0023 a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0021 a b) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0019 a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0017 a b) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0023 a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0021 a b) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb069_alpha_dummy_022), (nb069_alpha_dummy_025 a b)), ((nb069_alpha_dummy_021), (nb069_alpha_dummy_024 a b)), ((nb069_alpha_dummy_020), (nb069_alpha_dummy_023 a b)), ((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)), ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)), ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)), ((nb069_alpha_dummy_040), (nb069_alpha_dummy_041 a b)), ((nb069_alpha_dummy_038), (nb069_alpha_dummy_039 a b)), ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)), ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)), ((nb069_alpha_dummy_036), (nb069_alpha_dummy_037 a b)), ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)), ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a), ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))] (syn_c0) (nb069_wpp_refl_0004 x y a b))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0027 a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0025 a b) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0027 a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0025 a b) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0031 a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0029 a b) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0031 a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0029 a b) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb069_wpp_notmem_0084 : (nb069_alpha_dummy_040) ∉ ((syn_cnnc)).fv := by
  simpa only [nb069_alpha_dummy_040, fv_syn_cnnc] using (nb069_compact_fv_empty_0026)

theorem nb069_wpp_notmem_0085 (a : Var) (b : Var) : (nb069_alpha_dummy_041 a b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb069_alpha_dummy_041, fv_syn_cnnc] using (nb069_compact_fv_empty_0027 a b)

theorem nb069_wpp_notmem_0086 : (nb069_alpha_dummy_038) ∉ ((syn_cnnc)).fv := by
  simpa only [nb069_alpha_dummy_038, fv_syn_cnnc] using (nb069_compact_fv_empty_0028)

theorem nb069_wpp_notmem_0087 (a : Var) (b : Var) : (nb069_alpha_dummy_039 a b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb069_alpha_dummy_039, fv_syn_cnnc] using (nb069_compact_fv_empty_0029 a b)

theorem nb069_wpp_notmem_0088 : (nb069_alpha_dummy_036) ∉ ((syn_cnnc)).fv := by
  simpa only [nb069_alpha_dummy_036, fv_syn_cnnc] using (nb069_compact_fv_empty_0030)

theorem nb069_wpp_notmem_0089 (a : Var) (b : Var) : (nb069_alpha_dummy_037 a b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb069_alpha_dummy_037, fv_syn_cnnc] using (nb069_compact_fv_empty_0031 a b)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
