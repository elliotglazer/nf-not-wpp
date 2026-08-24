import NAR4H5C096M3Part001

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

theorem nb096_support_mem_0124 (D : Class) (R : Class) : (nb096_alpha_dummy_117 D R) ∈ (((Class.cv (nb096_alpha_dummy_117 D R))).fv ∪ ((Class.cv (nb096_alpha_dummy_117 D R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0125 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_120 D R q) ∈ (((Class.cv (nb096_alpha_dummy_120 D R q))).fv ∪ ((Class.cv (nb096_alpha_dummy_120 D R q))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0126 (D : Class) (R : Class) : (nb096_alpha_dummy_041 D R) ∈ (((Class.cv (nb096_alpha_dummy_042 D R))).fv ∪ ((Class.cv (nb096_alpha_dummy_041 D R))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0127 (D : Class) (R : Class) : (nb096_alpha_dummy_041 D R) ∈ (((syn_ccompl (Class.cab (nb096_alpha_dummy_101 D R) (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_042 D R)) (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R)) (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb096_alpha_dummy_101 D R) (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_041 D R)) (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R)) (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0126 D R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0126 D R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0128 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_043 D R q) ∈ (((Class.cv (nb096_alpha_dummy_044 D R q))).fv ∪ ((Class.cv (nb096_alpha_dummy_043 D R q))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0129 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_043 D R q) ∈ (((syn_ccompl (Class.cab (nb096_alpha_dummy_103 D R q) (syn_wrex (nb096_alpha_dummy_104 D R q) (Class.cv (nb096_alpha_dummy_044 D R q)) (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q)) (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))))))).fv ∪ ((syn_ccompl (Class.cab (nb096_alpha_dummy_103 D R q) (syn_wrex (nb096_alpha_dummy_104 D R q) (Class.cv (nb096_alpha_dummy_043 D R q)) (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q)) (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0128 D R q) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0128 D R q) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0130 (D : Class) (R : Class) : (nb096_alpha_dummy_041 D R) ∈ (((Class.cab (nb096_alpha_dummy_101 D R) (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_041 D R)) (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R)) (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_101 D R) (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_041 D R)) (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R)) (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0126 D R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0126 D R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0131 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_043 D R q) ∈ (((Class.cab (nb096_alpha_dummy_103 D R q) (syn_wrex (nb096_alpha_dummy_104 D R q) (Class.cv (nb096_alpha_dummy_043 D R q)) (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q)) (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_103 D R q) (syn_wrex (nb096_alpha_dummy_104 D R q) (Class.cv (nb096_alpha_dummy_043 D R q)) (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q)) (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0128 D R q) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0128 D R q) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0132 (D : Class) (R : Class) : (nb096_alpha_dummy_102 D R) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0133 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_104 D R q) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0134 (D : Class) (R : Class) : (nb096_alpha_dummy_102 D R) ∈ (((syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))).fv ∪ ((syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0135 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_104 D R q) ∈ (((syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))).fv ∪ ((syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_compact_fv_empty_0000 (D : Class) (R : Class) : (nb096_alpha_dummy_021 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0000 (D : Class) (R : Class) : (nb096_alpha_dummy_021 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_021, fv_syn_c1c] using (nb096_compact_fv_empty_0000 D R)

theorem nb096_compact_fv_empty_0001 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_024 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0001 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_024 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_024, fv_syn_c1c] using (nb096_compact_fv_empty_0001 D R q)

theorem nb096_compact_fv_empty_0002 (D : Class) (R : Class) : (nb096_alpha_dummy_020 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0002 (D : Class) (R : Class) : (nb096_alpha_dummy_020 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_020, fv_syn_c1c] using (nb096_compact_fv_empty_0002 D R)

theorem nb096_compact_fv_empty_0003 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_023 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0003 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_023 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_023, fv_syn_c1c] using (nb096_compact_fv_empty_0003 D R q)

theorem nb096_compact_fv_empty_0004 (D : Class) (R : Class) : (nb096_alpha_dummy_019 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0004 (D : Class) (R : Class) : (nb096_alpha_dummy_019 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_019, fv_syn_c1c] using (nb096_compact_fv_empty_0004 D R)

theorem nb096_compact_fv_empty_0005 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_022 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0005 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_022 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_022, fv_syn_c1c] using (nb096_compact_fv_empty_0005 D R q)

theorem nb096_compact_fv_empty_0006 (D : Class) (R : Class) : (nb096_alpha_dummy_017 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0006 (D : Class) (R : Class) : (nb096_alpha_dummy_017 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_017, fv_syn_c1c] using (nb096_compact_fv_empty_0006 D R)

theorem nb096_compact_fv_empty_0007 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_018 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0007 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_018 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_018, fv_syn_c1c] using (nb096_compact_fv_empty_0007 D R q)

theorem nb096_compact_fv_empty_0008 (D : Class) (R : Class) : (nb096_alpha_dummy_013 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0008 (D : Class) (R : Class) : (nb096_alpha_dummy_013 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_013, fv_syn_c1c] using (nb096_compact_fv_empty_0008 D R)

theorem nb096_compact_fv_empty_0009 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_015 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0009 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_015 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_015, fv_syn_c1c] using (nb096_compact_fv_empty_0009 D R q)

theorem nb096_compact_fv_empty_0010 (D : Class) (R : Class) : (nb096_alpha_dummy_014 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0010 (D : Class) (R : Class) : (nb096_alpha_dummy_014 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_014, fv_syn_c1c] using (nb096_compact_fv_empty_0010 D R)

theorem nb096_compact_fv_empty_0011 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_016 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0011 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_016 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_016, fv_syn_c1c] using (nb096_compact_fv_empty_0011 D R q)

theorem nb096_compact_fv_empty_0012 (D : Class) (R : Class) : (nb096_alpha_dummy_006 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0012 (D : Class) (R : Class) : (nb096_alpha_dummy_006 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_006, fv_syn_c1c] using (nb096_compact_fv_empty_0012 D R)

theorem nb096_compact_fv_empty_0013 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_008 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0013 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_008 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_008, fv_syn_c1c] using (nb096_compact_fv_empty_0013 D R q)

theorem nb096_compact_fv_empty_0014 (D : Class) (R : Class) : (nb096_alpha_dummy_005 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0014 (D : Class) (R : Class) : (nb096_alpha_dummy_005 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_005, fv_syn_c1c] using (nb096_compact_fv_empty_0014 D R)

theorem nb096_compact_fv_empty_0015 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_007 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0015 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_007 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_007, fv_syn_c1c] using (nb096_compact_fv_empty_0015 D R q)

theorem nb096_compact_fv_empty_0016 (D : Class) (R : Class) : (nb096_alpha_dummy_011 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0016 (D : Class) (R : Class) : (nb096_alpha_dummy_011 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_011, fv_syn_c1c] using (nb096_compact_fv_empty_0016 D R)

theorem nb096_compact_fv_empty_0017 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_012 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0017 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_012 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_012, fv_syn_c1c] using (nb096_compact_fv_empty_0017 D R q)

theorem nb096_compact_fv_empty_0018 (D : Class) (R : Class) : (nb096_alpha_dummy_009 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0018 (D : Class) (R : Class) : (nb096_alpha_dummy_009 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_009, fv_syn_c1c] using (nb096_compact_fv_empty_0018 D R)

theorem nb096_compact_fv_empty_0019 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_010 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0019 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_010 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_010, fv_syn_c1c] using (nb096_compact_fv_empty_0019 D R q)

theorem nb096_compact_fv_empty_0020 (D : Class) (R : Class) : (nb096_alpha_dummy_001 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0020 (D : Class) (R : Class) : (nb096_alpha_dummy_001 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_001, fv_syn_c1c] using (nb096_compact_fv_empty_0020 D R)

theorem nb096_compact_fv_empty_0021 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_002 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0021 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_002 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_002, fv_syn_c1c] using (nb096_compact_fv_empty_0021 D R q)

theorem nb096_compact_fv_empty_0022 (D : Class) (R : Class) : (nb096_alpha_dummy_000 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0022 (D : Class) (R : Class) : (nb096_alpha_dummy_000 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_000, fv_syn_c1c] using (nb096_compact_fv_empty_0022 D R)

theorem nb096_compact_fv_empty_0023 (q : Var) : q ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0023 (q : Var) : q ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb096_compact_fv_empty_0023 q)

theorem nb096_compact_fv_empty_0024 (D : Class) (R : Class) : (nb096_alpha_dummy_003 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0024 (D : Class) (R : Class) : (nb096_alpha_dummy_003 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_003, fv_syn_c1c] using (nb096_compact_fv_empty_0024 D R)

theorem nb096_compact_fv_empty_0025 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_004 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0025 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_004 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_004, fv_syn_c1c] using (nb096_compact_fv_empty_0025 D R q)

theorem nb096_compact_envfresh_0000 (D : Class) (R : Class) (q : Var) : TEnvFresh [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R), (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_011 D R), (nb096_alpha_dummy_012 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb096_alpha_dummy_021 D R) (nb096_alpha_dummy_024 D R q) (nb096_wpp_notmem_0000 D R) (nb096_wpp_notmem_0001 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_020 D R) (nb096_alpha_dummy_023 D R q) (nb096_wpp_notmem_0002 D R) (nb096_wpp_notmem_0003 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_019 D R) (nb096_alpha_dummy_022 D R q) (nb096_wpp_notmem_0004 D R) (nb096_wpp_notmem_0005 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_017 D R) (nb096_alpha_dummy_018 D R q) (nb096_wpp_notmem_0006 D R) (nb096_wpp_notmem_0007 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_013 D R) (nb096_alpha_dummy_015 D R q) (nb096_wpp_notmem_0008 D R) (nb096_wpp_notmem_0009 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_014 D R) (nb096_alpha_dummy_016 D R q) (nb096_wpp_notmem_0010 D R) (nb096_wpp_notmem_0011 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_006 D R) (nb096_alpha_dummy_008 D R q) (nb096_wpp_notmem_0012 D R) (nb096_wpp_notmem_0013 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_005 D R) (nb096_alpha_dummy_007 D R q) (nb096_wpp_notmem_0014 D R) (nb096_wpp_notmem_0015 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_011 D R) (nb096_alpha_dummy_012 D R q) (nb096_wpp_notmem_0016 D R) (nb096_wpp_notmem_0017 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_009 D R) (nb096_alpha_dummy_010 D R q) (nb096_wpp_notmem_0018 D R) (nb096_wpp_notmem_0019 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q) (nb096_wpp_notmem_0020 D R) (nb096_wpp_notmem_0021 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_wpp_notmem_0022 D R) (nb096_wpp_notmem_0023 q) (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q) (nb096_wpp_notmem_0024 D R) (nb096_wpp_notmem_0025 D R q) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))

noncomputable def nb096_wpp_refl_0000 (D : Class) (R : Class) (q : Var) : TReflOn [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R), (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_011 D R), (nb096_alpha_dummy_012 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0000 D R q)

theorem nb096_wpp_notmem_0026 (D : Class) (R : Class) : (nb096_alpha_dummy_021 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_021, fv_syn_c0] using (nb096_compact_fv_empty_0000 D R)

theorem nb096_wpp_notmem_0027 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_024 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_024, fv_syn_c0] using (nb096_compact_fv_empty_0001 D R q)

theorem nb096_wpp_notmem_0028 (D : Class) (R : Class) : (nb096_alpha_dummy_020 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_020, fv_syn_c0] using (nb096_compact_fv_empty_0002 D R)

theorem nb096_wpp_notmem_0029 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_023 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_023, fv_syn_c0] using (nb096_compact_fv_empty_0003 D R q)

theorem nb096_wpp_notmem_0030 (D : Class) (R : Class) : (nb096_alpha_dummy_019 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_019, fv_syn_c0] using (nb096_compact_fv_empty_0004 D R)

theorem nb096_wpp_notmem_0031 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_022 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_022, fv_syn_c0] using (nb096_compact_fv_empty_0005 D R q)

theorem nb096_wpp_notmem_0032 (D : Class) (R : Class) : (nb096_alpha_dummy_017 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_017, fv_syn_c0] using (nb096_compact_fv_empty_0006 D R)

theorem nb096_wpp_notmem_0033 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_018 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_018, fv_syn_c0] using (nb096_compact_fv_empty_0007 D R q)

theorem nb096_wpp_notmem_0034 (D : Class) (R : Class) : (nb096_alpha_dummy_013 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_013, fv_syn_c0] using (nb096_compact_fv_empty_0008 D R)

theorem nb096_wpp_notmem_0035 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_015 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_015, fv_syn_c0] using (nb096_compact_fv_empty_0009 D R q)

theorem nb096_wpp_notmem_0036 (D : Class) (R : Class) : (nb096_alpha_dummy_014 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_014, fv_syn_c0] using (nb096_compact_fv_empty_0010 D R)

theorem nb096_wpp_notmem_0037 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_016 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_016, fv_syn_c0] using (nb096_compact_fv_empty_0011 D R q)

theorem nb096_wpp_notmem_0038 (D : Class) (R : Class) : (nb096_alpha_dummy_006 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_006, fv_syn_c0] using (nb096_compact_fv_empty_0012 D R)

theorem nb096_wpp_notmem_0039 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_008 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_008, fv_syn_c0] using (nb096_compact_fv_empty_0013 D R q)

theorem nb096_wpp_notmem_0040 (D : Class) (R : Class) : (nb096_alpha_dummy_005 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_005, fv_syn_c0] using (nb096_compact_fv_empty_0014 D R)

theorem nb096_wpp_notmem_0041 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_007 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_007, fv_syn_c0] using (nb096_compact_fv_empty_0015 D R q)

theorem nb096_wpp_notmem_0042 (D : Class) (R : Class) : (nb096_alpha_dummy_011 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_011, fv_syn_c0] using (nb096_compact_fv_empty_0016 D R)

theorem nb096_wpp_notmem_0043 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_012 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_012, fv_syn_c0] using (nb096_compact_fv_empty_0017 D R q)

theorem nb096_wpp_notmem_0044 (D : Class) (R : Class) : (nb096_alpha_dummy_009 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_009, fv_syn_c0] using (nb096_compact_fv_empty_0018 D R)

theorem nb096_wpp_notmem_0045 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_010 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_010, fv_syn_c0] using (nb096_compact_fv_empty_0019 D R q)

theorem nb096_wpp_notmem_0046 (D : Class) (R : Class) : (nb096_alpha_dummy_001 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_001, fv_syn_c0] using (nb096_compact_fv_empty_0020 D R)

theorem nb096_wpp_notmem_0047 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_002 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_002, fv_syn_c0] using (nb096_compact_fv_empty_0021 D R q)

theorem nb096_wpp_notmem_0048 (D : Class) (R : Class) : (nb096_alpha_dummy_000 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_000, fv_syn_c0] using (nb096_compact_fv_empty_0022 D R)

theorem nb096_wpp_notmem_0049 (q : Var) : q ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb096_compact_fv_empty_0023 q)

theorem nb096_wpp_notmem_0050 (D : Class) (R : Class) : (nb096_alpha_dummy_003 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_003, fv_syn_c0] using (nb096_compact_fv_empty_0024 D R)

theorem nb096_wpp_notmem_0051 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_004 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_004, fv_syn_c0] using (nb096_compact_fv_empty_0025 D R q)

theorem nb096_compact_envfresh_0001 (D : Class) (R : Class) (q : Var) : TEnvFresh [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R), (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_011 D R), (nb096_alpha_dummy_012 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb096_alpha_dummy_021 D R) (nb096_alpha_dummy_024 D R q) (nb096_wpp_notmem_0026 D R) (nb096_wpp_notmem_0027 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_020 D R) (nb096_alpha_dummy_023 D R q) (nb096_wpp_notmem_0028 D R) (nb096_wpp_notmem_0029 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_019 D R) (nb096_alpha_dummy_022 D R q) (nb096_wpp_notmem_0030 D R) (nb096_wpp_notmem_0031 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_017 D R) (nb096_alpha_dummy_018 D R q) (nb096_wpp_notmem_0032 D R) (nb096_wpp_notmem_0033 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_013 D R) (nb096_alpha_dummy_015 D R q) (nb096_wpp_notmem_0034 D R) (nb096_wpp_notmem_0035 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_014 D R) (nb096_alpha_dummy_016 D R q) (nb096_wpp_notmem_0036 D R) (nb096_wpp_notmem_0037 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_006 D R) (nb096_alpha_dummy_008 D R q) (nb096_wpp_notmem_0038 D R) (nb096_wpp_notmem_0039 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_005 D R) (nb096_alpha_dummy_007 D R q) (nb096_wpp_notmem_0040 D R) (nb096_wpp_notmem_0041 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_011 D R) (nb096_alpha_dummy_012 D R q) (nb096_wpp_notmem_0042 D R) (nb096_wpp_notmem_0043 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_009 D R) (nb096_alpha_dummy_010 D R q) (nb096_wpp_notmem_0044 D R) (nb096_wpp_notmem_0045 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q) (nb096_wpp_notmem_0046 D R) (nb096_wpp_notmem_0047 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_wpp_notmem_0048 D R) (nb096_wpp_notmem_0049 q) (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q) (nb096_wpp_notmem_0050 D R) (nb096_wpp_notmem_0051 D R q) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))

noncomputable def nb096_wpp_refl_0001 (D : Class) (R : Class) (q : Var) : TReflOn [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R), (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_011 D R), (nb096_alpha_dummy_012 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0001 D R q)

theorem nb096_wpp_notmem_0052 (D : Class) (R : Class) : (nb096_alpha_dummy_017 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_017, fv_syn_cnnc] using (nb096_compact_fv_empty_0006 D R)

theorem nb096_wpp_notmem_0053 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_018 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_018, fv_syn_cnnc] using (nb096_compact_fv_empty_0007 D R q)

theorem nb096_wpp_notmem_0054 (D : Class) (R : Class) : (nb096_alpha_dummy_013 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_013, fv_syn_cnnc] using (nb096_compact_fv_empty_0008 D R)

theorem nb096_wpp_notmem_0055 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_015 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_015, fv_syn_cnnc] using (nb096_compact_fv_empty_0009 D R q)

theorem nb096_wpp_notmem_0056 (D : Class) (R : Class) : (nb096_alpha_dummy_014 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_014, fv_syn_cnnc] using (nb096_compact_fv_empty_0010 D R)

theorem nb096_wpp_notmem_0057 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_016 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_016, fv_syn_cnnc] using (nb096_compact_fv_empty_0011 D R q)

theorem nb096_wpp_notmem_0058 (D : Class) (R : Class) : (nb096_alpha_dummy_006 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_006, fv_syn_cnnc] using (nb096_compact_fv_empty_0012 D R)

theorem nb096_wpp_notmem_0059 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_008 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_008, fv_syn_cnnc] using (nb096_compact_fv_empty_0013 D R q)

theorem nb096_wpp_notmem_0060 (D : Class) (R : Class) : (nb096_alpha_dummy_005 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_005, fv_syn_cnnc] using (nb096_compact_fv_empty_0014 D R)

theorem nb096_wpp_notmem_0061 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_007 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_007, fv_syn_cnnc] using (nb096_compact_fv_empty_0015 D R q)

theorem nb096_wpp_notmem_0062 (D : Class) (R : Class) : (nb096_alpha_dummy_011 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_011, fv_syn_cnnc] using (nb096_compact_fv_empty_0016 D R)

theorem nb096_wpp_notmem_0063 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_012 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_012, fv_syn_cnnc] using (nb096_compact_fv_empty_0017 D R q)

theorem nb096_wpp_notmem_0064 (D : Class) (R : Class) : (nb096_alpha_dummy_009 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_009, fv_syn_cnnc] using (nb096_compact_fv_empty_0018 D R)

theorem nb096_wpp_notmem_0065 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_010 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_010, fv_syn_cnnc] using (nb096_compact_fv_empty_0019 D R q)

theorem nb096_wpp_notmem_0066 (D : Class) (R : Class) : (nb096_alpha_dummy_001 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_001, fv_syn_cnnc] using (nb096_compact_fv_empty_0020 D R)

theorem nb096_wpp_notmem_0067 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_002 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_002, fv_syn_cnnc] using (nb096_compact_fv_empty_0021 D R q)

theorem nb096_wpp_notmem_0068 (D : Class) (R : Class) : (nb096_alpha_dummy_000 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_000, fv_syn_cnnc] using (nb096_compact_fv_empty_0022 D R)

theorem nb096_wpp_notmem_0069 (q : Var) : q ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb096_compact_fv_empty_0023 q)

theorem nb096_wpp_notmem_0070 (D : Class) (R : Class) : (nb096_alpha_dummy_003 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_003, fv_syn_cnnc] using (nb096_compact_fv_empty_0024 D R)

theorem nb096_wpp_notmem_0071 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_004 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_004, fv_syn_cnnc] using (nb096_compact_fv_empty_0025 D R q)

theorem nb096_compact_envfresh_0002 (D : Class) (R : Class) (q : Var) : TEnvFresh [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_011 D R), (nb096_alpha_dummy_012 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb096_alpha_dummy_017 D R) (nb096_alpha_dummy_018 D R q) (nb096_wpp_notmem_0052 D R) (nb096_wpp_notmem_0053 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_013 D R) (nb096_alpha_dummy_015 D R q) (nb096_wpp_notmem_0054 D R) (nb096_wpp_notmem_0055 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_014 D R) (nb096_alpha_dummy_016 D R q) (nb096_wpp_notmem_0056 D R) (nb096_wpp_notmem_0057 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_006 D R) (nb096_alpha_dummy_008 D R q) (nb096_wpp_notmem_0058 D R) (nb096_wpp_notmem_0059 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_005 D R) (nb096_alpha_dummy_007 D R q) (nb096_wpp_notmem_0060 D R) (nb096_wpp_notmem_0061 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_011 D R) (nb096_alpha_dummy_012 D R q) (nb096_wpp_notmem_0062 D R) (nb096_wpp_notmem_0063 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_009 D R) (nb096_alpha_dummy_010 D R q) (nb096_wpp_notmem_0064 D R) (nb096_wpp_notmem_0065 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q) (nb096_wpp_notmem_0066 D R) (nb096_wpp_notmem_0067 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_wpp_notmem_0068 D R) (nb096_wpp_notmem_0069 q) (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q) (nb096_wpp_notmem_0070 D R) (nb096_wpp_notmem_0071 D R q) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))

noncomputable def nb096_wpp_refl_0002 (D : Class) (R : Class) (q : Var) : TReflOn [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_011 D R), (nb096_alpha_dummy_012 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0002 D R q)

theorem nb096_compact_fv_empty_0026 (D : Class) (R : Class) : (nb096_alpha_dummy_039 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0072 (D : Class) (R : Class) : (nb096_alpha_dummy_039 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_039, fv_syn_c1c] using (nb096_compact_fv_empty_0026 D R)

theorem nb096_compact_fv_empty_0027 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_040 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0073 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_040 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_040, fv_syn_c1c] using (nb096_compact_fv_empty_0027 D R q)

theorem nb096_compact_fv_empty_0028 (D : Class) (R : Class) : (nb096_alpha_dummy_037 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0074 (D : Class) (R : Class) : (nb096_alpha_dummy_037 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_037, fv_syn_c1c] using (nb096_compact_fv_empty_0028 D R)

theorem nb096_compact_fv_empty_0029 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_038 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0075 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_038 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_038, fv_syn_c1c] using (nb096_compact_fv_empty_0029 D R q)

theorem nb096_compact_fv_empty_0030 (D : Class) (R : Class) : (nb096_alpha_dummy_035 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0076 (D : Class) (R : Class) : (nb096_alpha_dummy_035 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_035, fv_syn_c1c] using (nb096_compact_fv_empty_0030 D R)

theorem nb096_compact_fv_empty_0031 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_036 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0077 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_036 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_036, fv_syn_c1c] using (nb096_compact_fv_empty_0031 D R q)

theorem nb096_compact_envfresh_0003 (D : Class) (R : Class) (q : Var) : TEnvFresh [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R), (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb096_alpha_dummy_021 D R) (nb096_alpha_dummy_024 D R q) (nb096_wpp_notmem_0000 D R) (nb096_wpp_notmem_0001 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_020 D R) (nb096_alpha_dummy_023 D R q) (nb096_wpp_notmem_0002 D R) (nb096_wpp_notmem_0003 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_019 D R) (nb096_alpha_dummy_022 D R q) (nb096_wpp_notmem_0004 D R) (nb096_wpp_notmem_0005 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_017 D R) (nb096_alpha_dummy_018 D R q) (nb096_wpp_notmem_0006 D R) (nb096_wpp_notmem_0007 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_013 D R) (nb096_alpha_dummy_015 D R q) (nb096_wpp_notmem_0008 D R) (nb096_wpp_notmem_0009 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_014 D R) (nb096_alpha_dummy_016 D R q) (nb096_wpp_notmem_0010 D R) (nb096_wpp_notmem_0011 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_039 D R) (nb096_alpha_dummy_040 D R q) (nb096_wpp_notmem_0072 D R) (nb096_wpp_notmem_0073 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_037 D R) (nb096_alpha_dummy_038 D R q) (nb096_wpp_notmem_0074 D R) (nb096_wpp_notmem_0075 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_006 D R) (nb096_alpha_dummy_008 D R q) (nb096_wpp_notmem_0012 D R) (nb096_wpp_notmem_0013 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_005 D R) (nb096_alpha_dummy_007 D R q) (nb096_wpp_notmem_0014 D R) (nb096_wpp_notmem_0015 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_035 D R) (nb096_alpha_dummy_036 D R q) (nb096_wpp_notmem_0076 D R) (nb096_wpp_notmem_0077 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_009 D R) (nb096_alpha_dummy_010 D R q) (nb096_wpp_notmem_0018 D R) (nb096_wpp_notmem_0019 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q) (nb096_wpp_notmem_0020 D R) (nb096_wpp_notmem_0021 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_wpp_notmem_0022 D R) (nb096_wpp_notmem_0023 q) (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q) (nb096_wpp_notmem_0024 D R) (nb096_wpp_notmem_0025 D R q) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb096_wpp_refl_0003 (D : Class) (R : Class) (q : Var) : TReflOn [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R), (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0003 D R q)

theorem nb096_wpp_notmem_0078 (D : Class) (R : Class) : (nb096_alpha_dummy_039 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_039, fv_syn_c0] using (nb096_compact_fv_empty_0026 D R)

theorem nb096_wpp_notmem_0079 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_040 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_040, fv_syn_c0] using (nb096_compact_fv_empty_0027 D R q)

theorem nb096_wpp_notmem_0080 (D : Class) (R : Class) : (nb096_alpha_dummy_037 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_037, fv_syn_c0] using (nb096_compact_fv_empty_0028 D R)

theorem nb096_wpp_notmem_0081 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_038 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_038, fv_syn_c0] using (nb096_compact_fv_empty_0029 D R q)

theorem nb096_wpp_notmem_0082 (D : Class) (R : Class) : (nb096_alpha_dummy_035 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_035, fv_syn_c0] using (nb096_compact_fv_empty_0030 D R)

theorem nb096_wpp_notmem_0083 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_036 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_036, fv_syn_c0] using (nb096_compact_fv_empty_0031 D R q)

theorem nb096_compact_envfresh_0004 (D : Class) (R : Class) (q : Var) : TEnvFresh [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R), (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb096_alpha_dummy_021 D R) (nb096_alpha_dummy_024 D R q) (nb096_wpp_notmem_0026 D R) (nb096_wpp_notmem_0027 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_020 D R) (nb096_alpha_dummy_023 D R q) (nb096_wpp_notmem_0028 D R) (nb096_wpp_notmem_0029 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_019 D R) (nb096_alpha_dummy_022 D R q) (nb096_wpp_notmem_0030 D R) (nb096_wpp_notmem_0031 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_017 D R) (nb096_alpha_dummy_018 D R q) (nb096_wpp_notmem_0032 D R) (nb096_wpp_notmem_0033 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_013 D R) (nb096_alpha_dummy_015 D R q) (nb096_wpp_notmem_0034 D R) (nb096_wpp_notmem_0035 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_014 D R) (nb096_alpha_dummy_016 D R q) (nb096_wpp_notmem_0036 D R) (nb096_wpp_notmem_0037 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_039 D R) (nb096_alpha_dummy_040 D R q) (nb096_wpp_notmem_0078 D R) (nb096_wpp_notmem_0079 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_037 D R) (nb096_alpha_dummy_038 D R q) (nb096_wpp_notmem_0080 D R) (nb096_wpp_notmem_0081 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_006 D R) (nb096_alpha_dummy_008 D R q) (nb096_wpp_notmem_0038 D R) (nb096_wpp_notmem_0039 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_005 D R) (nb096_alpha_dummy_007 D R q) (nb096_wpp_notmem_0040 D R) (nb096_wpp_notmem_0041 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_035 D R) (nb096_alpha_dummy_036 D R q) (nb096_wpp_notmem_0082 D R) (nb096_wpp_notmem_0083 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_009 D R) (nb096_alpha_dummy_010 D R q) (nb096_wpp_notmem_0044 D R) (nb096_wpp_notmem_0045 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q) (nb096_wpp_notmem_0046 D R) (nb096_wpp_notmem_0047 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_wpp_notmem_0048 D R) (nb096_wpp_notmem_0049 q) (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q) (nb096_wpp_notmem_0050 D R) (nb096_wpp_notmem_0051 D R q) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))

noncomputable def nb096_wpp_refl_0004 (D : Class) (R : Class) (q : Var) : TReflOn [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R), (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0004 D R q)

theorem nb096_wpp_notmem_0084 (D : Class) (R : Class) : (nb096_alpha_dummy_039 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_039, fv_syn_cnnc] using (nb096_compact_fv_empty_0026 D R)

theorem nb096_wpp_notmem_0085 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_040 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_040, fv_syn_cnnc] using (nb096_compact_fv_empty_0027 D R q)

theorem nb096_wpp_notmem_0086 (D : Class) (R : Class) : (nb096_alpha_dummy_037 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_037, fv_syn_cnnc] using (nb096_compact_fv_empty_0028 D R)

theorem nb096_wpp_notmem_0087 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_038 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_038, fv_syn_cnnc] using (nb096_compact_fv_empty_0029 D R q)

theorem nb096_wpp_notmem_0088 (D : Class) (R : Class) : (nb096_alpha_dummy_035 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_035, fv_syn_cnnc] using (nb096_compact_fv_empty_0030 D R)

theorem nb096_wpp_notmem_0089 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_036 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_036, fv_syn_cnnc] using (nb096_compact_fv_empty_0031 D R q)

theorem nb096_compact_envfresh_0005 (D : Class) (R : Class) (q : Var) : TEnvFresh [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb096_alpha_dummy_017 D R) (nb096_alpha_dummy_018 D R q) (nb096_wpp_notmem_0052 D R) (nb096_wpp_notmem_0053 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_013 D R) (nb096_alpha_dummy_015 D R q) (nb096_wpp_notmem_0054 D R) (nb096_wpp_notmem_0055 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_014 D R) (nb096_alpha_dummy_016 D R q) (nb096_wpp_notmem_0056 D R) (nb096_wpp_notmem_0057 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_039 D R) (nb096_alpha_dummy_040 D R q) (nb096_wpp_notmem_0084 D R) (nb096_wpp_notmem_0085 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_037 D R) (nb096_alpha_dummy_038 D R q) (nb096_wpp_notmem_0086 D R) (nb096_wpp_notmem_0087 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_006 D R) (nb096_alpha_dummy_008 D R q) (nb096_wpp_notmem_0058 D R) (nb096_wpp_notmem_0059 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_005 D R) (nb096_alpha_dummy_007 D R q) (nb096_wpp_notmem_0060 D R) (nb096_wpp_notmem_0061 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_035 D R) (nb096_alpha_dummy_036 D R q) (nb096_wpp_notmem_0088 D R) (nb096_wpp_notmem_0089 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_009 D R) (nb096_alpha_dummy_010 D R q) (nb096_wpp_notmem_0064 D R) (nb096_wpp_notmem_0065 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q) (nb096_wpp_notmem_0066 D R) (nb096_wpp_notmem_0067 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_wpp_notmem_0068 D R) (nb096_wpp_notmem_0069 q) (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q) (nb096_wpp_notmem_0070 D R) (nb096_wpp_notmem_0071 D R q) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))

noncomputable def nb096_wpp_refl_0005 (D : Class) (R : Class) (q : Var) : TReflOn [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0005 D R q)

theorem nb096_wpp_notmem_0090 (D : Class) (R : Class) : (nb096_alpha_dummy_037 D R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_037, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0028 D R)

theorem nb096_wpp_notmem_0091 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_038 D R q) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_038, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0029 D R q)

theorem nb096_wpp_notmem_0092 (D : Class) (R : Class) : (nb096_alpha_dummy_006 D R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_006, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0012 D R)

theorem nb096_wpp_notmem_0093 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_008 D R q) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_008, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0013 D R q)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

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

theorem nb096_wpp_notmem_0094 (D : Class) (R : Class) : (nb096_alpha_dummy_005 D R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_005, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0014 D R)

theorem nb096_wpp_notmem_0095 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_007 D R q) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_007, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0015 D R q)

theorem nb096_wpp_notmem_0096 (D : Class) (R : Class) : (nb096_alpha_dummy_035 D R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_035, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0030 D R)

theorem nb096_wpp_notmem_0097 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_036 D R q) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_036, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0031 D R q)

theorem nb096_wpp_notmem_0098 (D : Class) (R : Class) : (nb096_alpha_dummy_009 D R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_009, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0018 D R)

theorem nb096_wpp_notmem_0099 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_010 D R q) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_010, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0019 D R q)

theorem nb096_wpp_notmem_0100 (D : Class) (R : Class) : (nb096_alpha_dummy_001 D R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_001, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0020 D R)

theorem nb096_wpp_notmem_0101 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_002 D R q) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_002, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0021 D R q)

theorem nb096_wpp_notmem_0102 (D : Class) (R : Class) : (nb096_alpha_dummy_000 D R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_000, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0022 D R)

theorem nb096_wpp_notmem_0103 (q : Var) : q ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0023 q)

theorem nb096_wpp_notmem_0104 (D : Class) (R : Class) : (nb096_alpha_dummy_003 D R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_003, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0024 D R)

theorem nb096_wpp_notmem_0105 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_004 D R q) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_004, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0025 D R q)

theorem nb096_compact_envfresh_0006 (D : Class) (R : Class) (q : Var) : TEnvFresh [((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb096_alpha_dummy_037 D R) (nb096_alpha_dummy_038 D R q) (nb096_wpp_notmem_0090 D R) (nb096_wpp_notmem_0091 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_006 D R) (nb096_alpha_dummy_008 D R q) (nb096_wpp_notmem_0092 D R) (nb096_wpp_notmem_0093 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_005 D R) (nb096_alpha_dummy_007 D R q) (nb096_wpp_notmem_0094 D R) (nb096_wpp_notmem_0095 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_035 D R) (nb096_alpha_dummy_036 D R q) (nb096_wpp_notmem_0096 D R) (nb096_wpp_notmem_0097 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_009 D R) (nb096_alpha_dummy_010 D R q) (nb096_wpp_notmem_0098 D R) (nb096_wpp_notmem_0099 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q) (nb096_wpp_notmem_0100 D R) (nb096_wpp_notmem_0101 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_wpp_notmem_0102 D R) (nb096_wpp_notmem_0103 q) (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q) (nb096_wpp_notmem_0104 D R) (nb096_wpp_notmem_0105 D R q) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))

noncomputable def nb096_wpp_refl_0006 (D : Class) (R : Class) (q : Var) : TReflOn [((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0006 D R q)

noncomputable def nb096_split_alpha_0000 (D : Class) (R : Class) (q : Var) : TAlphaWff [((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (Wff.neg (Wff.classMem (Class.cv (nb096_alpha_dummy_035 D R)) (Class.cab (nb096_alpha_dummy_005 D R) (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_001 D R)) (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R)) (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R))) (syn_csn (syn_c0c)))))))) (Wff.neg (Wff.classMem (Class.cv (nb096_alpha_dummy_036 D R q)) (Class.cab (nb096_alpha_dummy_007 D R q) (syn_wrex (nb096_alpha_dummy_008 D R q) (Class.cv (nb096_alpha_dummy_002 D R q)) (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q)) (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q))) (syn_csn (syn_c0c)))))))) :=
  (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0034 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0036 D R q) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0034 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0036 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0038 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0039 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0035 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0037 D R q) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_000 D R))).fv ∪ ((Class.cv (nb096_alpha_dummy_001 D R))).fv) (by decide)) (freshVar_injective (((Class.cv q)).fv ∪ ((Class.cv (nb096_alpha_dummy_002 D R q))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0012 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0013 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0012 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0013 D R q) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0042 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0043 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0040 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0041 D R q) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_006 D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_008 D R q))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0016 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0017 D R q) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0016 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0017 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0014 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0015 D R q) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R), (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c1c) (nb096_wpp_refl_0003 D R q))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0020 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0021 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0018 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0019 D R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0024 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0025 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0022 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0023 D R q) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0020 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0021 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0018 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0019 D R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0024 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0025 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0022 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0023 D R q) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R), (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c0) (nb096_wpp_refl_0004 D R q))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0028 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0029 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0026 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0027 D R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0028 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0029 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0026 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0027 D R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0032 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0033 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0030 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0031 D R q) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0032 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0033 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0030 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0031 D R q) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0014 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0015 D R q) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (nb096_wpp_refl_0005 D R q))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0014 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0015 D R q) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0014 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0015 D R q) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (nb096_wpp_refl_0005 D R q)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0012 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0013 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0012 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0013 D R q) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0042 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0043 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0040 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0041 D R q) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_006 D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_008 D R q))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0016 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0017 D R q) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0016 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0017 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0014 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0015 D R q) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R), (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c1c) (nb096_wpp_refl_0003 D R q))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0020 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0021 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0018 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0019 D R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0024 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0025 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0022 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0023 D R q) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0020 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0021 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0018 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0019 D R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0024 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0025 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0022 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0023 D R q) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R), (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c0) (nb096_wpp_refl_0004 D R q))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0028 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0029 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0026 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0027 D R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0028 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0029 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0026 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0027 D R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0032 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0033 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0030 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0031 D R q) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0032 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0033 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0030 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0031 D R q) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0014 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0015 D R q) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (nb096_wpp_refl_0005 D R q))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0014 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0015 D R q) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0014 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0015 D R q) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (nb096_wpp_refl_0005 D R q)))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_ccompl (syn_csn (syn_c0c))) (nb096_wpp_refl_0006 D R q))))))))))))))))))

noncomputable def nb096_split_alpha_0001 (D : Class) (R : Class) (q : Var) : TAlphaWff [((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (Wff.imp (Wff.classMem (Class.cv (nb096_alpha_dummy_035 D R)) (Class.cab (nb096_alpha_dummy_005 D R) (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_001 D R)) (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R)) (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb096_alpha_dummy_035 D R)) (Class.cab (nb096_alpha_dummy_005 D R) (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_001 D R)) (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R)) (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R))) (syn_csn (syn_c0c))))))))) (Wff.imp (Wff.classMem (Class.cv (nb096_alpha_dummy_036 D R q)) (Class.cab (nb096_alpha_dummy_007 D R q) (syn_wrex (nb096_alpha_dummy_008 D R q) (Class.cv (nb096_alpha_dummy_002 D R q)) (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q)) (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb096_alpha_dummy_036 D R q)) (Class.cab (nb096_alpha_dummy_007 D R q) (syn_wrex (nb096_alpha_dummy_008 D R q) (Class.cv (nb096_alpha_dummy_002 D R q)) (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q)) (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q))) (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0034 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0036 D R q) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0034 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0036 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0038 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0039 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0035 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0037 D R q) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_000 D R))).fv ∪ ((Class.cv (nb096_alpha_dummy_001 D R))).fv) (by decide)) (freshVar_injective (((Class.cv q)).fv ∪ ((Class.cv (nb096_alpha_dummy_002 D R q))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0012 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0013 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0012 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0013 D R q) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0042 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0043 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0040 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0041 D R q) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_006 D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_008 D R q))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0016 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0017 D R q) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0016 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0017 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0014 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0015 D R q) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R), (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c1c) (nb096_wpp_refl_0003 D R q))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0020 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0021 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0018 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0019 D R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0024 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0025 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0022 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0023 D R q) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0020 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0021 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0018 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0019 D R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0024 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0025 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0022 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0023 D R q) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R), (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c0) (nb096_wpp_refl_0004 D R q))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0028 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0029 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0026 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0027 D R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0028 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0029 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0026 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0027 D R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0032 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0033 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0030 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0031 D R q) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0032 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0033 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0030 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0031 D R q) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0014 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0015 D R q) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (nb096_wpp_refl_0005 D R q))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0014 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0015 D R q) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0014 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0015 D R q) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (nb096_wpp_refl_0005 D R q)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0012 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0013 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0012 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0013 D R q) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0042 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0043 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0040 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0041 D R q) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_006 D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_008 D R q))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0016 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0017 D R q) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0016 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0017 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0014 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0015 D R q) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R), (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c1c) (nb096_wpp_refl_0003 D R q))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0020 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0021 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0018 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0019 D R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0024 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0025 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0022 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0023 D R q) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0020 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0021 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0018 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0019 D R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0024 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0025 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0022 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0023 D R q) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R), (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c0) (nb096_wpp_refl_0004 D R q))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0028 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0029 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0026 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0027 D R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0028 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0029 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0026 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0027 D R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0032 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0033 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0030 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0031 D R q) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0032 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0033 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0030 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0031 D R q) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0014 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0015 D R q) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (nb096_wpp_refl_0005 D R q))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0014 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0015 D R q) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0014 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0015 D R q) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (nb096_wpp_refl_0005 D R q)))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_ccompl (syn_csn (syn_c0c))) (nb096_wpp_refl_0006 D R q))))))))))))))))) (nb096_split_alpha_0000 D R q))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

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

noncomputable def nb096_split_alpha_0002 (D : Class) (R : Class) (q : Var) : TAlphaWff [((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (Wff.classEq (Class.cv (nb096_alpha_dummy_003 D R)) (syn_cop (Class.cv (nb096_alpha_dummy_000 D R)) (Class.cv (nb096_alpha_dummy_001 D R)))) (Wff.classEq (Class.cv (nb096_alpha_dummy_004 D R q)) (syn_cop (Class.cv q) (Class.cv (nb096_alpha_dummy_002 D R q)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0002 D R) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0003 D R q) 0))) (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0000 D R) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0001 D R q) 0))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0006 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0008 D R q) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0006 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0008 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0010 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0011 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0007 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0009 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0004 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0005 D R q) 0)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_000 D R))).fv ∪ ((Class.cv (nb096_alpha_dummy_001 D R))).fv) (by decide)) (freshVar_injective (((Class.cv q)).fv ∪ ((Class.cv (nb096_alpha_dummy_002 D R q))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0012 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0013 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0012 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0013 D R q) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_006 D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_008 D R q))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0016 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0017 D R q) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0016 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0017 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0014 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0015 D R q) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R), (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_011 D R), (nb096_alpha_dummy_012 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c1c) (nb096_wpp_refl_0000 D R q))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0020 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0021 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0018 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0019 D R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0024 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0025 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0022 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0023 D R q) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0020 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0021 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0018 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0019 D R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0024 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0025 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0022 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0023 D R q) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R), (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_011 D R), (nb096_alpha_dummy_012 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c0) (nb096_wpp_refl_0001 D R q))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0028 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0029 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0026 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0027 D R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0028 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0029 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0026 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0027 D R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0032 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0033 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0030 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0031 D R q) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0032 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0033 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0030 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0031 D R q) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0014 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0015 D R q) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_011 D R), (nb096_alpha_dummy_012 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (nb096_wpp_refl_0002 D R q))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0014 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0015 D R q) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0014 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0015 D R q) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_011 D R), (nb096_alpha_dummy_012 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (nb096_wpp_refl_0002 D R q)))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0006 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0008 D R q) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0006 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0008 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0010 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0011 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0007 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0009 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0004 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0005 D R q) 0)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_000 D R))).fv ∪ ((Class.cv (nb096_alpha_dummy_001 D R))).fv) (by decide)) (freshVar_injective (((Class.cv q)).fv ∪ ((Class.cv (nb096_alpha_dummy_002 D R q))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0012 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0013 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0012 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0013 D R q) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_006 D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_008 D R q))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0016 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0017 D R q) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0016 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0017 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0014 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0015 D R q) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R), (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_011 D R), (nb096_alpha_dummy_012 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c1c) (nb096_wpp_refl_0000 D R q))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0020 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0021 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0018 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0019 D R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0024 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0025 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0022 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0023 D R q) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0020 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0021 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0018 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0019 D R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0024 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0025 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0022 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0023 D R q) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R), (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_011 D R), (nb096_alpha_dummy_012 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c0) (nb096_wpp_refl_0001 D R q))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0028 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0029 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0026 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0027 D R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0028 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0029 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0026 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0027 D R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0032 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0033 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0030 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0031 D R q) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0032 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0033 D R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0030 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0031 D R q) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0014 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0015 D R q) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_011 D R), (nb096_alpha_dummy_012 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (nb096_wpp_refl_0002 D R q))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0014 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0015 D R q) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0014 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0015 D R q) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)), ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_011 D R), (nb096_alpha_dummy_012 D R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (nb096_wpp_refl_0002 D R q)))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb096_split_alpha_0001 D R q)))))))))))

theorem nb096_focused_notmem_0000 (D : Class) (R : Class) : (nb096_alpha_dummy_001 D R) ∉ D.fv := by
  change freshVar (({(nb096_alpha_dummy_000 D R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪ ((syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv) 0 ∉ D.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_right _ (((fv_syn_cpw1 (syn_cpw1 D)).symm ▸ (((fv_syn_cpw1 D).symm ▸ (hu)))))))

theorem nb096_wpp_notmem_0106 (D : Class) (R : Class) : (nb096_alpha_dummy_001 D R) ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
  simpa only [nb096_alpha_dummy_001, fv_syn_cpw1] using (nb096_focused_notmem_0000 D R)

theorem nb096_focused_notmem_0001 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_002 D R q) ∉ D.fv := by
  change freshVar (({q} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪ ((syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv) 0 ∉ D.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_right _ (((fv_syn_cpw1 (syn_cpw1 D)).symm ▸ (((fv_syn_cpw1 D).symm ▸ (hu)))))))

theorem nb096_wpp_notmem_0107 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_002 D R q) ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
  simpa only [nb096_alpha_dummy_002, fv_syn_cpw1] using (nb096_focused_notmem_0001 D R q)

theorem nb096_focused_notmem_0002 (D : Class) (R : Class) : (nb096_alpha_dummy_000 D R) ∉ D.fv := by
  change freshVar ((R).fv ∪ (D).fv) 0 ∉ D.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_right _ (hu))

theorem nb096_wpp_notmem_0108 (D : Class) (R : Class) : (nb096_alpha_dummy_000 D R) ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
  simpa only [nb096_alpha_dummy_000, fv_syn_cpw1] using (nb096_focused_notmem_0002 D R)

theorem nb096_wpp_notmem_0109 (D : Class) (q : Var) (dv_D_q : q ∉ D.fv) : q ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
  simpa only [fv_syn_cpw1] using dv_D_q

theorem nb096_focused_notmem_0003 (D : Class) (R : Class) : (nb096_alpha_dummy_003 D R) ∉ D.fv := by
  change freshVar (({(nb096_alpha_dummy_000 D R)} : Finset Var) ∪ ({(nb096_alpha_dummy_001 D R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb096_alpha_dummy_000 D R)) (syn_cpw1 (syn_cpw1 D))) (Wff.classEq (Class.cv (nb096_alpha_dummy_001 D R)) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))))).fv) 0 ∉ D.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_right _ (((fv_syn_wa (Wff.classMem (Class.cv (nb096_alpha_dummy_000 D R)) (syn_cpw1 (syn_cpw1 D))) (Wff.classEq (Class.cv (nb096_alpha_dummy_001 D R)) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))))).symm ▸ (Finset.mem_union_left _ (((fv_wff_classMem (Class.cv (nb096_alpha_dummy_000 D R)) (syn_cpw1 (syn_cpw1 D))).symm ▸ (Finset.mem_union_right _ (((fv_syn_cpw1 (syn_cpw1 D)).symm ▸ (((fv_syn_cpw1 D).symm ▸ (hu))))))))))))

theorem nb096_wpp_notmem_0110 (D : Class) (R : Class) : (nb096_alpha_dummy_003 D R) ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
  simpa only [nb096_alpha_dummy_003, fv_syn_cpw1] using (nb096_focused_notmem_0003 D R)

theorem nb096_focused_notmem_0004 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_004 D R q) ∉ D.fv := by
  change freshVar (({q} : Finset Var) ∪ ({(nb096_alpha_dummy_002 D R q)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv q) (syn_cpw1 (syn_cpw1 D))) (Wff.classEq (Class.cv (nb096_alpha_dummy_002 D R q)) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))))).fv) 0 ∉ D.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_right _ (((fv_syn_wa (Wff.classMem (Class.cv q) (syn_cpw1 (syn_cpw1 D))) (Wff.classEq (Class.cv (nb096_alpha_dummy_002 D R q)) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))))).symm ▸ (Finset.mem_union_left _ (((fv_wff_classMem (Class.cv q) (syn_cpw1 (syn_cpw1 D))).symm ▸ (Finset.mem_union_right _ (((fv_syn_cpw1 (syn_cpw1 D)).symm ▸ (((fv_syn_cpw1 D).symm ▸ (hu))))))))))))

theorem nb096_wpp_notmem_0111 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_004 D R q) ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
  simpa only [nb096_alpha_dummy_004, fv_syn_cpw1] using (nb096_focused_notmem_0004 D R q)

theorem nb096_compact_envfresh_0007 (D : Class) (R : Class) (q : Var) (dv_D_q : q ∉ D.fv) : TEnvFresh [((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_cpw1 (syn_cpw1 D))).fv := by
  exact (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q) (nb096_wpp_notmem_0106 D R) (nb096_wpp_notmem_0107 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_wpp_notmem_0108 D R) (nb096_wpp_notmem_0109 D q dv_D_q) (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q) (nb096_wpp_notmem_0110 D R) (nb096_wpp_notmem_0111 D R q) (TEnvFresh.nil ((syn_cpw1 (syn_cpw1 D))).fv))))

noncomputable def nb096_wpp_refl_0007 (D : Class) (R : Class) (q : Var) (dv_D_q : q ∉ D.fv) : TReflOn [((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_cpw1 (syn_cpw1 D))).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0007 D R q dv_D_q)

theorem nb096_focused_notmem_0005 (D : Class) (R : Class) : (nb096_alpha_dummy_049 D R) ∉ D.fv := by
  change freshVar ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))).fv) 0 ∉ D.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb096_focused_notmem_0006 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_050 D R q) ∉ D.fv := by
  change freshVar ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))).fv) 0 ∉ D.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb096_focused_notmem_0007 (D : Class) (R : Class) : (nb096_alpha_dummy_047 D R) ∉ D.fv := by
  change freshVar (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).fv ∪ ((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).fv) 0 ∉ D.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_left _ (((fv_syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))).symm ▸ (Finset.mem_union_left _ (hu)))))

theorem nb096_focused_notmem_0008 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_048 D R q) ∉ D.fv := by
  change freshVar (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).fv ∪ ((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).fv) 0 ∉ D.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_left _ (((fv_syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))).symm ▸ (Finset.mem_union_left _ (hu)))))

theorem nb096_focused_notmem_0009 (D : Class) (R : Class) : (nb096_alpha_dummy_045 D R) ∉ D.fv := by
  change freshVar (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).fv) 0 ∉ D.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => ((fv_syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))).symm ▸ (Finset.mem_union_left _ (hu))))

theorem nb096_focused_notmem_0010 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_046 D R q) ∉ D.fv := by
  change freshVar (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).fv) 0 ∉ D.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => ((fv_syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))).symm ▸ (Finset.mem_union_left _ (hu))))

theorem nb096_focused_notmem_0011 (D : Class) (R : Class) : (nb096_alpha_dummy_042 D R) ∉ D.fv := by
  change freshVar (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv) 1 ∉ D.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun _ hu => Finset.mem_union_right _ (((fv_syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).symm ▸ (((fv_syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))).symm ▸ (Finset.mem_union_left _ (hu)))))))

theorem nb096_focused_notmem_0012 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_044 D R q) ∉ D.fv := by
  change freshVar (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv) 1 ∉ D.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun _ hu => Finset.mem_union_right _ (((fv_syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).symm ▸ (((fv_syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))).symm ▸ (Finset.mem_union_left _ (hu)))))))

theorem nb096_focused_notmem_0013 (D : Class) (R : Class) : (nb096_alpha_dummy_041 D R) ∉ D.fv := by
  change freshVar (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv) 0 ∉ D.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_right _ (((fv_syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).symm ▸ (((fv_syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))).symm ▸ (Finset.mem_union_left _ (hu)))))))

theorem nb096_focused_notmem_0014 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_043 D R q) ∉ D.fv := by
  change freshVar (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv) 0 ∉ D.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_right _ (((fv_syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).symm ▸ (((fv_syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))).symm ▸ (Finset.mem_union_left _ (hu)))))))

theorem nb096_compact_envfresh_0008 (D : Class) (R : Class) (q : Var) (dv_D_q : q ∉ D.fv) : TEnvFresh [((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] D.fv := by
  exact (TEnvFresh.consFresh (nb096_alpha_dummy_049 D R) (nb096_alpha_dummy_050 D R q) (nb096_focused_notmem_0005 D R) (nb096_focused_notmem_0006 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_047 D R) (nb096_alpha_dummy_048 D R q) (nb096_focused_notmem_0007 D R) (nb096_focused_notmem_0008 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_045 D R) (nb096_alpha_dummy_046 D R q) (nb096_focused_notmem_0009 D R) (nb096_focused_notmem_0010 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_042 D R) (nb096_alpha_dummy_044 D R q) (nb096_focused_notmem_0011 D R) (nb096_focused_notmem_0012 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_041 D R) (nb096_alpha_dummy_043 D R q) (nb096_focused_notmem_0013 D R) (nb096_focused_notmem_0014 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q) (nb096_focused_notmem_0000 D R) (nb096_focused_notmem_0001 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_focused_notmem_0002 D R) dv_D_q (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q) (nb096_focused_notmem_0003 D R) (nb096_focused_notmem_0004 D R q) (TEnvFresh.nil D.fv)))))))))

noncomputable def nb096_focused_refl_0000 (D : Class) (R : Class) (q : Var) (dv_D_q : q ∉ D.fv) : TReflOn [((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] D.fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0008 D R q dv_D_q)

theorem nb096_compact_fv_empty_0032 (D : Class) (R : Class) : (nb096_alpha_dummy_081 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0112 (D : Class) (R : Class) : (nb096_alpha_dummy_081 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_081, fv_syn_c1c] using (nb096_compact_fv_empty_0032 D R)

theorem nb096_compact_fv_empty_0033 (R : Class) (q : Var) : (nb096_alpha_dummy_084 R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0113 (R : Class) (q : Var) : (nb096_alpha_dummy_084 R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_084, fv_syn_c1c] using (nb096_compact_fv_empty_0033 R q)

theorem nb096_compact_fv_empty_0034 (D : Class) (R : Class) : (nb096_alpha_dummy_080 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0114 (D : Class) (R : Class) : (nb096_alpha_dummy_080 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_080, fv_syn_c1c] using (nb096_compact_fv_empty_0034 D R)

theorem nb096_compact_fv_empty_0035 (R : Class) (q : Var) : (nb096_alpha_dummy_083 R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0115 (R : Class) (q : Var) : (nb096_alpha_dummy_083 R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_083, fv_syn_c1c] using (nb096_compact_fv_empty_0035 R q)

theorem nb096_compact_fv_empty_0036 (D : Class) (R : Class) : (nb096_alpha_dummy_079 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0116 (D : Class) (R : Class) : (nb096_alpha_dummy_079 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_079, fv_syn_c1c] using (nb096_compact_fv_empty_0036 D R)

theorem nb096_compact_fv_empty_0037 (R : Class) (q : Var) : (nb096_alpha_dummy_082 R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0117 (R : Class) (q : Var) : (nb096_alpha_dummy_082 R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_082, fv_syn_c1c] using (nb096_compact_fv_empty_0037 R q)

theorem nb096_compact_fv_empty_0038 (D : Class) (R : Class) : (nb096_alpha_dummy_077 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0118 (D : Class) (R : Class) : (nb096_alpha_dummy_077 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_077, fv_syn_c1c] using (nb096_compact_fv_empty_0038 D R)

theorem nb096_compact_fv_empty_0039 (R : Class) (q : Var) : (nb096_alpha_dummy_078 R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0119 (R : Class) (q : Var) : (nb096_alpha_dummy_078 R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_078, fv_syn_c1c] using (nb096_compact_fv_empty_0039 R q)

theorem nb096_compact_fv_empty_0040 (D : Class) (R : Class) : (nb096_alpha_dummy_073 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0120 (D : Class) (R : Class) : (nb096_alpha_dummy_073 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_073, fv_syn_c1c] using (nb096_compact_fv_empty_0040 D R)

theorem nb096_compact_fv_empty_0041 (R : Class) (q : Var) : (nb096_alpha_dummy_075 R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0121 (R : Class) (q : Var) : (nb096_alpha_dummy_075 R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_075, fv_syn_c1c] using (nb096_compact_fv_empty_0041 R q)

theorem nb096_compact_fv_empty_0042 (D : Class) (R : Class) : (nb096_alpha_dummy_074 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0122 (D : Class) (R : Class) : (nb096_alpha_dummy_074 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_074, fv_syn_c1c] using (nb096_compact_fv_empty_0042 D R)

theorem nb096_compact_fv_empty_0043 (R : Class) (q : Var) : (nb096_alpha_dummy_076 R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0123 (R : Class) (q : Var) : (nb096_alpha_dummy_076 R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_076, fv_syn_c1c] using (nb096_compact_fv_empty_0043 R q)

theorem nb096_compact_fv_empty_0044 (D : Class) (R : Class) : (nb096_alpha_dummy_066 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0124 (D : Class) (R : Class) : (nb096_alpha_dummy_066 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_066, fv_syn_c1c] using (nb096_compact_fv_empty_0044 D R)

theorem nb096_compact_fv_empty_0045 (R : Class) (q : Var) : (nb096_alpha_dummy_068 R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0125 (R : Class) (q : Var) : (nb096_alpha_dummy_068 R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_068, fv_syn_c1c] using (nb096_compact_fv_empty_0045 R q)

theorem nb096_compact_fv_empty_0046 (D : Class) (R : Class) : (nb096_alpha_dummy_065 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0126 (D : Class) (R : Class) : (nb096_alpha_dummy_065 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_065, fv_syn_c1c] using (nb096_compact_fv_empty_0046 D R)

theorem nb096_compact_fv_empty_0047 (R : Class) (q : Var) : (nb096_alpha_dummy_067 R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0127 (R : Class) (q : Var) : (nb096_alpha_dummy_067 R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_067, fv_syn_c1c] using (nb096_compact_fv_empty_0047 R q)

theorem nb096_compact_fv_empty_0048 (D : Class) (R : Class) : (nb096_alpha_dummy_071 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0128 (D : Class) (R : Class) : (nb096_alpha_dummy_071 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_071, fv_syn_c1c] using (nb096_compact_fv_empty_0048 D R)

theorem nb096_compact_fv_empty_0049 (R : Class) (q : Var) : (nb096_alpha_dummy_072 R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0129 (R : Class) (q : Var) : (nb096_alpha_dummy_072 R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_072, fv_syn_c1c] using (nb096_compact_fv_empty_0049 R q)

theorem nb096_compact_fv_empty_0050 (D : Class) (R : Class) : (nb096_alpha_dummy_069 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0130 (D : Class) (R : Class) : (nb096_alpha_dummy_069 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_069, fv_syn_c1c] using (nb096_compact_fv_empty_0050 D R)

theorem nb096_compact_fv_empty_0051 (R : Class) (q : Var) : (nb096_alpha_dummy_070 R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0131 (R : Class) (q : Var) : (nb096_alpha_dummy_070 R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_070, fv_syn_c1c] using (nb096_compact_fv_empty_0051 R q)

theorem nb096_compact_fv_empty_0052 (D : Class) (R : Class) : (nb096_alpha_dummy_052 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0132 (D : Class) (R : Class) : (nb096_alpha_dummy_052 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_052, fv_syn_c1c] using (nb096_compact_fv_empty_0052 D R)

theorem nb096_compact_fv_empty_0053 (R : Class) (q : Var) : (nb096_alpha_dummy_054 R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0133 (R : Class) (q : Var) : (nb096_alpha_dummy_054 R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_054, fv_syn_c1c] using (nb096_compact_fv_empty_0053 R q)

theorem nb096_compact_fv_empty_0054 (D : Class) (R : Class) : (nb096_alpha_dummy_051 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0134 (D : Class) (R : Class) : (nb096_alpha_dummy_051 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_051, fv_syn_c1c] using (nb096_compact_fv_empty_0054 D R)

theorem nb096_compact_fv_empty_0055 (R : Class) (q : Var) : (nb096_alpha_dummy_053 R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0135 (R : Class) (q : Var) : (nb096_alpha_dummy_053 R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_053, fv_syn_c1c] using (nb096_compact_fv_empty_0055 R q)

theorem nb096_compact_fv_empty_0056 (D : Class) (R : Class) : (nb096_alpha_dummy_049 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0136 (D : Class) (R : Class) : (nb096_alpha_dummy_049 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_049, fv_syn_c1c] using (nb096_compact_fv_empty_0056 D R)

theorem nb096_compact_fv_empty_0057 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_050 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0137 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_050 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_050, fv_syn_c1c] using (nb096_compact_fv_empty_0057 D R q)

theorem nb096_compact_fv_empty_0058 (D : Class) (R : Class) : (nb096_alpha_dummy_047 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0138 (D : Class) (R : Class) : (nb096_alpha_dummy_047 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_047, fv_syn_c1c] using (nb096_compact_fv_empty_0058 D R)

theorem nb096_compact_fv_empty_0059 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_048 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0139 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_048 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_048, fv_syn_c1c] using (nb096_compact_fv_empty_0059 D R q)

theorem nb096_compact_fv_empty_0060 (D : Class) (R : Class) : (nb096_alpha_dummy_045 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0140 (D : Class) (R : Class) : (nb096_alpha_dummy_045 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_045, fv_syn_c1c] using (nb096_compact_fv_empty_0060 D R)

theorem nb096_compact_fv_empty_0061 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_046 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0141 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_046 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_046, fv_syn_c1c] using (nb096_compact_fv_empty_0061 D R q)

theorem nb096_compact_fv_empty_0062 (D : Class) (R : Class) : (nb096_alpha_dummy_042 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0142 (D : Class) (R : Class) : (nb096_alpha_dummy_042 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_042, fv_syn_c1c] using (nb096_compact_fv_empty_0062 D R)

theorem nb096_compact_fv_empty_0063 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_044 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0143 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_044 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_044, fv_syn_c1c] using (nb096_compact_fv_empty_0063 D R q)

theorem nb096_compact_fv_empty_0064 (D : Class) (R : Class) : (nb096_alpha_dummy_041 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0144 (D : Class) (R : Class) : (nb096_alpha_dummy_041 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_041, fv_syn_c1c] using (nb096_compact_fv_empty_0064 D R)

theorem nb096_compact_fv_empty_0065 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_043 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0145 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_043 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_043, fv_syn_c1c] using (nb096_compact_fv_empty_0065 D R q)

theorem nb096_compact_envfresh_0009 (D : Class) (R : Class) (q : Var) : TEnvFresh [((nb096_alpha_dummy_081 D R), (nb096_alpha_dummy_084 R q)), ((nb096_alpha_dummy_080 D R), (nb096_alpha_dummy_083 R q)), ((nb096_alpha_dummy_079 D R), (nb096_alpha_dummy_082 R q)), ((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_071 D R), (nb096_alpha_dummy_072 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb096_alpha_dummy_081 D R) (nb096_alpha_dummy_084 R q) (nb096_wpp_notmem_0112 D R) (nb096_wpp_notmem_0113 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_080 D R) (nb096_alpha_dummy_083 R q) (nb096_wpp_notmem_0114 D R) (nb096_wpp_notmem_0115 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_079 D R) (nb096_alpha_dummy_082 R q) (nb096_wpp_notmem_0116 D R) (nb096_wpp_notmem_0117 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_077 D R) (nb096_alpha_dummy_078 R q) (nb096_wpp_notmem_0118 D R) (nb096_wpp_notmem_0119 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_073 D R) (nb096_alpha_dummy_075 R q) (nb096_wpp_notmem_0120 D R) (nb096_wpp_notmem_0121 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_074 D R) (nb096_alpha_dummy_076 R q) (nb096_wpp_notmem_0122 D R) (nb096_wpp_notmem_0123 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_066 D R) (nb096_alpha_dummy_068 R q) (nb096_wpp_notmem_0124 D R) (nb096_wpp_notmem_0125 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_065 D R) (nb096_alpha_dummy_067 R q) (nb096_wpp_notmem_0126 D R) (nb096_wpp_notmem_0127 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_071 D R) (nb096_alpha_dummy_072 R q) (nb096_wpp_notmem_0128 D R) (nb096_wpp_notmem_0129 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_069 D R) (nb096_alpha_dummy_070 R q) (nb096_wpp_notmem_0130 D R) (nb096_wpp_notmem_0131 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_052 D R) (nb096_alpha_dummy_054 R q) (nb096_wpp_notmem_0132 D R) (nb096_wpp_notmem_0133 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_051 D R) (nb096_alpha_dummy_053 R q) (nb096_wpp_notmem_0134 D R) (nb096_wpp_notmem_0135 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_049 D R) (nb096_alpha_dummy_050 D R q) (nb096_wpp_notmem_0136 D R) (nb096_wpp_notmem_0137 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_047 D R) (nb096_alpha_dummy_048 D R q) (nb096_wpp_notmem_0138 D R) (nb096_wpp_notmem_0139 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_045 D R) (nb096_alpha_dummy_046 D R q) (nb096_wpp_notmem_0140 D R) (nb096_wpp_notmem_0141 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_042 D R) (nb096_alpha_dummy_044 D R q) (nb096_wpp_notmem_0142 D R) (nb096_wpp_notmem_0143 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_041 D R) (nb096_alpha_dummy_043 D R q) (nb096_wpp_notmem_0144 D R) (nb096_wpp_notmem_0145 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q) (nb096_wpp_notmem_0020 D R) (nb096_wpp_notmem_0021 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_wpp_notmem_0022 D R) (nb096_wpp_notmem_0023 q) (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q) (nb096_wpp_notmem_0024 D R) (nb096_wpp_notmem_0025 D R q) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))

noncomputable def nb096_wpp_refl_0008 (D : Class) (R : Class) (q : Var) : TReflOn [((nb096_alpha_dummy_081 D R), (nb096_alpha_dummy_084 R q)), ((nb096_alpha_dummy_080 D R), (nb096_alpha_dummy_083 R q)), ((nb096_alpha_dummy_079 D R), (nb096_alpha_dummy_082 R q)), ((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_071 D R), (nb096_alpha_dummy_072 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0009 D R q)

theorem nb096_wpp_notmem_0146 (D : Class) (R : Class) : (nb096_alpha_dummy_081 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_081, fv_syn_c0] using (nb096_compact_fv_empty_0032 D R)

theorem nb096_wpp_notmem_0147 (R : Class) (q : Var) : (nb096_alpha_dummy_084 R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_084, fv_syn_c0] using (nb096_compact_fv_empty_0033 R q)

theorem nb096_wpp_notmem_0148 (D : Class) (R : Class) : (nb096_alpha_dummy_080 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_080, fv_syn_c0] using (nb096_compact_fv_empty_0034 D R)

theorem nb096_wpp_notmem_0149 (R : Class) (q : Var) : (nb096_alpha_dummy_083 R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_083, fv_syn_c0] using (nb096_compact_fv_empty_0035 R q)

theorem nb096_wpp_notmem_0150 (D : Class) (R : Class) : (nb096_alpha_dummy_079 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_079, fv_syn_c0] using (nb096_compact_fv_empty_0036 D R)

theorem nb096_wpp_notmem_0151 (R : Class) (q : Var) : (nb096_alpha_dummy_082 R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_082, fv_syn_c0] using (nb096_compact_fv_empty_0037 R q)

theorem nb096_wpp_notmem_0152 (D : Class) (R : Class) : (nb096_alpha_dummy_077 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_077, fv_syn_c0] using (nb096_compact_fv_empty_0038 D R)

theorem nb096_wpp_notmem_0153 (R : Class) (q : Var) : (nb096_alpha_dummy_078 R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_078, fv_syn_c0] using (nb096_compact_fv_empty_0039 R q)

theorem nb096_wpp_notmem_0154 (D : Class) (R : Class) : (nb096_alpha_dummy_073 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_073, fv_syn_c0] using (nb096_compact_fv_empty_0040 D R)

theorem nb096_wpp_notmem_0155 (R : Class) (q : Var) : (nb096_alpha_dummy_075 R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_075, fv_syn_c0] using (nb096_compact_fv_empty_0041 R q)

theorem nb096_wpp_notmem_0156 (D : Class) (R : Class) : (nb096_alpha_dummy_074 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_074, fv_syn_c0] using (nb096_compact_fv_empty_0042 D R)

theorem nb096_wpp_notmem_0157 (R : Class) (q : Var) : (nb096_alpha_dummy_076 R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_076, fv_syn_c0] using (nb096_compact_fv_empty_0043 R q)

theorem nb096_wpp_notmem_0158 (D : Class) (R : Class) : (nb096_alpha_dummy_066 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_066, fv_syn_c0] using (nb096_compact_fv_empty_0044 D R)

theorem nb096_wpp_notmem_0159 (R : Class) (q : Var) : (nb096_alpha_dummy_068 R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_068, fv_syn_c0] using (nb096_compact_fv_empty_0045 R q)

theorem nb096_wpp_notmem_0160 (D : Class) (R : Class) : (nb096_alpha_dummy_065 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_065, fv_syn_c0] using (nb096_compact_fv_empty_0046 D R)

theorem nb096_wpp_notmem_0161 (R : Class) (q : Var) : (nb096_alpha_dummy_067 R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_067, fv_syn_c0] using (nb096_compact_fv_empty_0047 R q)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
