import NAR4C076C001Part004

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

theorem nb076_support_mem_0176 : (nb076_alpha_dummy_002) ∈ (((Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002))) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002))) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0172) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0172) 1))
    ·
      rw [fv_syn_cxp]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0177 (g : Var) (a : Var) (b : Var) : g ∈ (((Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g)) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g)) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0174 g a b) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0174 g a b) 1))
    ·
      rw [fv_syn_cxp]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0178 : (nb076_alpha_dummy_002) ∈ (({(nb076_alpha_dummy_113)} : Finset Var) ∪ ({(nb076_alpha_dummy_114)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_113)) (Class.cv (nb076_alpha_dummy_001))) (Wff.classMem (Class.cv (nb076_alpha_dummy_114)) (Class.cv (nb076_alpha_dummy_002))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wa]
  apply Finset.mem_union_right
  rw [fv_wff_classMem]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0179 (g : Var) (b : Var) : g ∈ (({(nb076_alpha_dummy_115 g b)} : Finset Var) ∪ ({(nb076_alpha_dummy_116 g b)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_115 g b)) (Class.cv b)) (Wff.classMem (Class.cv (nb076_alpha_dummy_116 g b)) (Class.cv g)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wa]
  apply Finset.mem_union_right
  rw [fv_wff_classMem]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0180 : (nb076_alpha_dummy_002) ∈ (((Class.cv (nb076_alpha_dummy_001))).fv ∪ ((Class.cv (nb076_alpha_dummy_002))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0181 (g : Var) (b : Var) : g ∈ (((Class.cv b)).fv ∪ ((Class.cv g)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0182 : (nb076_alpha_dummy_082) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_082))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0183 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_084 g a b) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0184 : (nb076_alpha_dummy_082) ∈ (((syn_cphi (Class.cv (nb076_alpha_dummy_082)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_082)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0185 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_084 g a b) ∈ (((syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_compact_fv_empty_0000 : (nb076_alpha_dummy_033) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0000 : (nb076_alpha_dummy_033) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_033, fv_syn_c1c] using (nb076_compact_fv_empty_0000)

theorem nb076_compact_fv_empty_0001 (m : Var) (n : Var) : (nb076_alpha_dummy_036 m n) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0001 (m : Var) (n : Var) : (nb076_alpha_dummy_036 m n) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_036, fv_syn_c1c] using (nb076_compact_fv_empty_0001 m n)

theorem nb076_compact_fv_empty_0002 : (nb076_alpha_dummy_032) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0002 : (nb076_alpha_dummy_032) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_032, fv_syn_c1c] using (nb076_compact_fv_empty_0002)

theorem nb076_compact_fv_empty_0003 (m : Var) (n : Var) : (nb076_alpha_dummy_035 m n) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0003 (m : Var) (n : Var) : (nb076_alpha_dummy_035 m n) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_035, fv_syn_c1c] using (nb076_compact_fv_empty_0003 m n)

theorem nb076_compact_fv_empty_0004 : (nb076_alpha_dummy_031) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0004 : (nb076_alpha_dummy_031) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_031, fv_syn_c1c] using (nb076_compact_fv_empty_0004)

theorem nb076_compact_fv_empty_0005 (m : Var) (n : Var) : (nb076_alpha_dummy_034 m n) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0005 (m : Var) (n : Var) : (nb076_alpha_dummy_034 m n) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_034, fv_syn_c1c] using (nb076_compact_fv_empty_0005 m n)

theorem nb076_compact_fv_empty_0006 : (nb076_alpha_dummy_029) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0006 : (nb076_alpha_dummy_029) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_029, fv_syn_c1c] using (nb076_compact_fv_empty_0006)

theorem nb076_compact_fv_empty_0007 (m : Var) (n : Var) : (nb076_alpha_dummy_030 m n) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0007 (m : Var) (n : Var) : (nb076_alpha_dummy_030 m n) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_030, fv_syn_c1c] using (nb076_compact_fv_empty_0007 m n)

theorem nb076_compact_fv_empty_0008 : (nb076_alpha_dummy_025) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0008 : (nb076_alpha_dummy_025) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_025, fv_syn_c1c] using (nb076_compact_fv_empty_0008)

theorem nb076_compact_fv_empty_0009 (m : Var) (n : Var) : (nb076_alpha_dummy_027 m n) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0009 (m : Var) (n : Var) : (nb076_alpha_dummy_027 m n) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_027, fv_syn_c1c] using (nb076_compact_fv_empty_0009 m n)

theorem nb076_compact_fv_empty_0010 : (nb076_alpha_dummy_026) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0010 : (nb076_alpha_dummy_026) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_026, fv_syn_c1c] using (nb076_compact_fv_empty_0010)

theorem nb076_compact_fv_empty_0011 (m : Var) (n : Var) : (nb076_alpha_dummy_028 m n) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0011 (m : Var) (n : Var) : (nb076_alpha_dummy_028 m n) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_028, fv_syn_c1c] using (nb076_compact_fv_empty_0011 m n)

theorem nb076_compact_fv_empty_0012 : (nb076_alpha_dummy_018) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0012 : (nb076_alpha_dummy_018) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_018, fv_syn_c1c] using (nb076_compact_fv_empty_0012)

theorem nb076_compact_fv_empty_0013 (m : Var) (n : Var) : (nb076_alpha_dummy_020 m n) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0013 (m : Var) (n : Var) : (nb076_alpha_dummy_020 m n) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_020, fv_syn_c1c] using (nb076_compact_fv_empty_0013 m n)

theorem nb076_compact_fv_empty_0014 : (nb076_alpha_dummy_017) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0014 : (nb076_alpha_dummy_017) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_017, fv_syn_c1c] using (nb076_compact_fv_empty_0014)

theorem nb076_compact_fv_empty_0015 (m : Var) (n : Var) : (nb076_alpha_dummy_019 m n) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0015 (m : Var) (n : Var) : (nb076_alpha_dummy_019 m n) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_019, fv_syn_c1c] using (nb076_compact_fv_empty_0015 m n)

theorem nb076_compact_fv_empty_0016 : (nb076_alpha_dummy_023) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0016 : (nb076_alpha_dummy_023) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_023, fv_syn_c1c] using (nb076_compact_fv_empty_0016)

theorem nb076_compact_fv_empty_0017 (m : Var) (n : Var) : (nb076_alpha_dummy_024 m n) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0017 (m : Var) (n : Var) : (nb076_alpha_dummy_024 m n) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_024, fv_syn_c1c] using (nb076_compact_fv_empty_0017 m n)

theorem nb076_compact_fv_empty_0018 : (nb076_alpha_dummy_021) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0018 : (nb076_alpha_dummy_021) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_021, fv_syn_c1c] using (nb076_compact_fv_empty_0018)

theorem nb076_compact_fv_empty_0019 (m : Var) (n : Var) : (nb076_alpha_dummy_022 m n) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0019 (m : Var) (n : Var) : (nb076_alpha_dummy_022 m n) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_022, fv_syn_c1c] using (nb076_compact_fv_empty_0019 m n)

theorem nb076_compact_fv_empty_0020 : (nb076_alpha_dummy_010) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0020 : (nb076_alpha_dummy_010) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_010, fv_syn_c1c] using (nb076_compact_fv_empty_0020)

theorem nb076_compact_fv_empty_0021 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_012 g m n a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0021 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_012 g m n a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_012, fv_syn_c1c] using (nb076_compact_fv_empty_0021 g m n a b)

theorem nb076_compact_fv_empty_0022 : (nb076_alpha_dummy_009) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0022 : (nb076_alpha_dummy_009) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_009, fv_syn_c1c] using (nb076_compact_fv_empty_0022)

theorem nb076_compact_fv_empty_0023 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_011 g m n a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0023 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_011 g m n a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_011, fv_syn_c1c] using (nb076_compact_fv_empty_0023 g m n a b)

theorem nb076_compact_fv_empty_0024 : (nb076_alpha_dummy_015) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0024 : (nb076_alpha_dummy_015) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_015, fv_syn_c1c] using (nb076_compact_fv_empty_0024)

theorem nb076_compact_fv_empty_0025 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_016 g m n a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0025 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_016 g m n a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_016, fv_syn_c1c] using (nb076_compact_fv_empty_0025 g m n a b)

theorem nb076_compact_fv_empty_0026 : (nb076_alpha_dummy_013) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0026 : (nb076_alpha_dummy_013) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_013, fv_syn_c1c] using (nb076_compact_fv_empty_0026)

theorem nb076_compact_fv_empty_0027 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_014 g m n a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0027 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_014 g m n a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_014, fv_syn_c1c] using (nb076_compact_fv_empty_0027 g m n a b)

theorem nb076_compact_fv_empty_0028 : (nb076_alpha_dummy_005) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0028 : (nb076_alpha_dummy_005) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_005, fv_syn_c1c] using (nb076_compact_fv_empty_0028)

theorem nb076_compact_fv_empty_0029 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_006 g m n a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0029 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_006 g m n a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_006, fv_syn_c1c] using (nb076_compact_fv_empty_0029 g m n a b)

theorem nb076_compact_fv_empty_0030 : (nb076_alpha_dummy_004) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0030 : (nb076_alpha_dummy_004) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_004, fv_syn_c1c] using (nb076_compact_fv_empty_0030)

theorem nb076_compact_fv_empty_0031 (n : Var) : n ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0031 (n : Var) : n ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb076_compact_fv_empty_0031 n)

theorem nb076_compact_fv_empty_0032 : (nb076_alpha_dummy_003) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0032 : (nb076_alpha_dummy_003) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_003, fv_syn_c1c] using (nb076_compact_fv_empty_0032)

theorem nb076_compact_fv_empty_0033 (m : Var) : m ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0033 (m : Var) : m ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb076_compact_fv_empty_0033 m)

theorem nb076_compact_fv_empty_0034 : (nb076_alpha_dummy_007) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0034 : (nb076_alpha_dummy_007) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_007, fv_syn_c1c] using (nb076_compact_fv_empty_0034)

theorem nb076_compact_fv_empty_0035 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_008 g m n a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0035 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_008 g m n a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_008, fv_syn_c1c] using (nb076_compact_fv_empty_0035 g m n a b)

theorem nb076_compact_envfresh_0000 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : TEnvFresh [((nb076_alpha_dummy_033), (nb076_alpha_dummy_036 m n)), ((nb076_alpha_dummy_032), (nb076_alpha_dummy_035 m n)), ((nb076_alpha_dummy_031), (nb076_alpha_dummy_034 m n)), ((nb076_alpha_dummy_029), (nb076_alpha_dummy_030 m n)), ((nb076_alpha_dummy_025), (nb076_alpha_dummy_027 m n)), ((nb076_alpha_dummy_026), (nb076_alpha_dummy_028 m n)), ((nb076_alpha_dummy_018), (nb076_alpha_dummy_020 m n)), ((nb076_alpha_dummy_017), (nb076_alpha_dummy_019 m n)), ((nb076_alpha_dummy_023), (nb076_alpha_dummy_024 m n)), ((nb076_alpha_dummy_021), (nb076_alpha_dummy_022 m n)), ((nb076_alpha_dummy_010), (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009), (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_015), (nb076_alpha_dummy_016 g m n a b)), ((nb076_alpha_dummy_013), (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb076_alpha_dummy_033) (nb076_alpha_dummy_036 m n) (nb076_wpp_notmem_0000) (nb076_wpp_notmem_0001 m n) (TEnvFresh.consFresh (nb076_alpha_dummy_032) (nb076_alpha_dummy_035 m n) (nb076_wpp_notmem_0002) (nb076_wpp_notmem_0003 m n) (TEnvFresh.consFresh (nb076_alpha_dummy_031) (nb076_alpha_dummy_034 m n) (nb076_wpp_notmem_0004) (nb076_wpp_notmem_0005 m n) (TEnvFresh.consFresh (nb076_alpha_dummy_029) (nb076_alpha_dummy_030 m n) (nb076_wpp_notmem_0006) (nb076_wpp_notmem_0007 m n) (TEnvFresh.consFresh (nb076_alpha_dummy_025) (nb076_alpha_dummy_027 m n) (nb076_wpp_notmem_0008) (nb076_wpp_notmem_0009 m n) (TEnvFresh.consFresh (nb076_alpha_dummy_026) (nb076_alpha_dummy_028 m n) (nb076_wpp_notmem_0010) (nb076_wpp_notmem_0011 m n) (TEnvFresh.consFresh (nb076_alpha_dummy_018) (nb076_alpha_dummy_020 m n) (nb076_wpp_notmem_0012) (nb076_wpp_notmem_0013 m n) (TEnvFresh.consFresh (nb076_alpha_dummy_017) (nb076_alpha_dummy_019 m n) (nb076_wpp_notmem_0014) (nb076_wpp_notmem_0015 m n) (TEnvFresh.consFresh (nb076_alpha_dummy_023) (nb076_alpha_dummy_024 m n) (nb076_wpp_notmem_0016) (nb076_wpp_notmem_0017 m n) (TEnvFresh.consFresh (nb076_alpha_dummy_021) (nb076_alpha_dummy_022 m n) (nb076_wpp_notmem_0018) (nb076_wpp_notmem_0019 m n) (TEnvFresh.consFresh (nb076_alpha_dummy_010) (nb076_alpha_dummy_012 g m n a b) (nb076_wpp_notmem_0020) (nb076_wpp_notmem_0021 g m n a b) (TEnvFresh.consFresh (nb076_alpha_dummy_009) (nb076_alpha_dummy_011 g m n a b) (nb076_wpp_notmem_0022) (nb076_wpp_notmem_0023 g m n a b) (TEnvFresh.consFresh (nb076_alpha_dummy_015) (nb076_alpha_dummy_016 g m n a b) (nb076_wpp_notmem_0024) (nb076_wpp_notmem_0025 g m n a b) (TEnvFresh.consFresh (nb076_alpha_dummy_013) (nb076_alpha_dummy_014 g m n a b) (nb076_wpp_notmem_0026) (nb076_wpp_notmem_0027 g m n a b) (TEnvFresh.consFresh (nb076_alpha_dummy_005) (nb076_alpha_dummy_006 g m n a b) (nb076_wpp_notmem_0028) (nb076_wpp_notmem_0029 g m n a b) (TEnvFresh.consFresh (nb076_alpha_dummy_004) n (nb076_wpp_notmem_0030) (nb076_wpp_notmem_0031 n) (TEnvFresh.consFresh (nb076_alpha_dummy_003) m (nb076_wpp_notmem_0032) (nb076_wpp_notmem_0033 m) (TEnvFresh.consFresh (nb076_alpha_dummy_007) (nb076_alpha_dummy_008 g m n a b) (nb076_wpp_notmem_0034) (nb076_wpp_notmem_0035 g m n a b) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))

noncomputable def nb076_wpp_refl_0000 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : TReflOn [((nb076_alpha_dummy_033), (nb076_alpha_dummy_036 m n)), ((nb076_alpha_dummy_032), (nb076_alpha_dummy_035 m n)), ((nb076_alpha_dummy_031), (nb076_alpha_dummy_034 m n)), ((nb076_alpha_dummy_029), (nb076_alpha_dummy_030 m n)), ((nb076_alpha_dummy_025), (nb076_alpha_dummy_027 m n)), ((nb076_alpha_dummy_026), (nb076_alpha_dummy_028 m n)), ((nb076_alpha_dummy_018), (nb076_alpha_dummy_020 m n)), ((nb076_alpha_dummy_017), (nb076_alpha_dummy_019 m n)), ((nb076_alpha_dummy_023), (nb076_alpha_dummy_024 m n)), ((nb076_alpha_dummy_021), (nb076_alpha_dummy_022 m n)), ((nb076_alpha_dummy_010), (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009), (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_015), (nb076_alpha_dummy_016 g m n a b)), ((nb076_alpha_dummy_013), (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb076_compact_envfresh_0000 g m n a b)

theorem nb076_wpp_notmem_0036 : (nb076_alpha_dummy_033) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_033, fv_syn_c0] using (nb076_compact_fv_empty_0000)

theorem nb076_wpp_notmem_0037 (m : Var) (n : Var) : (nb076_alpha_dummy_036 m n) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_036, fv_syn_c0] using (nb076_compact_fv_empty_0001 m n)

theorem nb076_wpp_notmem_0038 : (nb076_alpha_dummy_032) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_032, fv_syn_c0] using (nb076_compact_fv_empty_0002)

theorem nb076_wpp_notmem_0039 (m : Var) (n : Var) : (nb076_alpha_dummy_035 m n) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_035, fv_syn_c0] using (nb076_compact_fv_empty_0003 m n)

theorem nb076_wpp_notmem_0040 : (nb076_alpha_dummy_031) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_031, fv_syn_c0] using (nb076_compact_fv_empty_0004)

theorem nb076_wpp_notmem_0041 (m : Var) (n : Var) : (nb076_alpha_dummy_034 m n) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_034, fv_syn_c0] using (nb076_compact_fv_empty_0005 m n)

theorem nb076_wpp_notmem_0042 : (nb076_alpha_dummy_029) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_029, fv_syn_c0] using (nb076_compact_fv_empty_0006)

theorem nb076_wpp_notmem_0043 (m : Var) (n : Var) : (nb076_alpha_dummy_030 m n) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_030, fv_syn_c0] using (nb076_compact_fv_empty_0007 m n)

theorem nb076_wpp_notmem_0044 : (nb076_alpha_dummy_025) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_025, fv_syn_c0] using (nb076_compact_fv_empty_0008)

theorem nb076_wpp_notmem_0045 (m : Var) (n : Var) : (nb076_alpha_dummy_027 m n) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_027, fv_syn_c0] using (nb076_compact_fv_empty_0009 m n)

theorem nb076_wpp_notmem_0046 : (nb076_alpha_dummy_026) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_026, fv_syn_c0] using (nb076_compact_fv_empty_0010)

theorem nb076_wpp_notmem_0047 (m : Var) (n : Var) : (nb076_alpha_dummy_028 m n) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_028, fv_syn_c0] using (nb076_compact_fv_empty_0011 m n)

theorem nb076_wpp_notmem_0048 : (nb076_alpha_dummy_018) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_018, fv_syn_c0] using (nb076_compact_fv_empty_0012)

theorem nb076_wpp_notmem_0049 (m : Var) (n : Var) : (nb076_alpha_dummy_020 m n) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_020, fv_syn_c0] using (nb076_compact_fv_empty_0013 m n)

theorem nb076_wpp_notmem_0050 : (nb076_alpha_dummy_017) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_017, fv_syn_c0] using (nb076_compact_fv_empty_0014)

theorem nb076_wpp_notmem_0051 (m : Var) (n : Var) : (nb076_alpha_dummy_019 m n) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_019, fv_syn_c0] using (nb076_compact_fv_empty_0015 m n)

theorem nb076_wpp_notmem_0052 : (nb076_alpha_dummy_023) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_023, fv_syn_c0] using (nb076_compact_fv_empty_0016)

theorem nb076_wpp_notmem_0053 (m : Var) (n : Var) : (nb076_alpha_dummy_024 m n) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_024, fv_syn_c0] using (nb076_compact_fv_empty_0017 m n)

theorem nb076_wpp_notmem_0054 : (nb076_alpha_dummy_021) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_021, fv_syn_c0] using (nb076_compact_fv_empty_0018)

theorem nb076_wpp_notmem_0055 (m : Var) (n : Var) : (nb076_alpha_dummy_022 m n) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_022, fv_syn_c0] using (nb076_compact_fv_empty_0019 m n)

theorem nb076_wpp_notmem_0056 : (nb076_alpha_dummy_010) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_010, fv_syn_c0] using (nb076_compact_fv_empty_0020)

theorem nb076_wpp_notmem_0057 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_012 g m n a b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_012, fv_syn_c0] using (nb076_compact_fv_empty_0021 g m n a b)

theorem nb076_wpp_notmem_0058 : (nb076_alpha_dummy_009) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_009, fv_syn_c0] using (nb076_compact_fv_empty_0022)

theorem nb076_wpp_notmem_0059 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_011 g m n a b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_011, fv_syn_c0] using (nb076_compact_fv_empty_0023 g m n a b)

theorem nb076_wpp_notmem_0060 : (nb076_alpha_dummy_015) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_015, fv_syn_c0] using (nb076_compact_fv_empty_0024)

theorem nb076_wpp_notmem_0061 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_016 g m n a b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_016, fv_syn_c0] using (nb076_compact_fv_empty_0025 g m n a b)

theorem nb076_wpp_notmem_0062 : (nb076_alpha_dummy_013) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_013, fv_syn_c0] using (nb076_compact_fv_empty_0026)

theorem nb076_wpp_notmem_0063 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_014 g m n a b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_014, fv_syn_c0] using (nb076_compact_fv_empty_0027 g m n a b)

theorem nb076_wpp_notmem_0064 : (nb076_alpha_dummy_005) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_005, fv_syn_c0] using (nb076_compact_fv_empty_0028)

theorem nb076_wpp_notmem_0065 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_006 g m n a b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_006, fv_syn_c0] using (nb076_compact_fv_empty_0029 g m n a b)

theorem nb076_wpp_notmem_0066 : (nb076_alpha_dummy_004) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_004, fv_syn_c0] using (nb076_compact_fv_empty_0030)

theorem nb076_wpp_notmem_0067 (n : Var) : n ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb076_compact_fv_empty_0031 n)

theorem nb076_wpp_notmem_0068 : (nb076_alpha_dummy_003) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_003, fv_syn_c0] using (nb076_compact_fv_empty_0032)

theorem nb076_wpp_notmem_0069 (m : Var) : m ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb076_compact_fv_empty_0033 m)

theorem nb076_wpp_notmem_0070 : (nb076_alpha_dummy_007) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_007, fv_syn_c0] using (nb076_compact_fv_empty_0034)

theorem nb076_wpp_notmem_0071 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_008 g m n a b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_008, fv_syn_c0] using (nb076_compact_fv_empty_0035 g m n a b)

theorem nb076_compact_envfresh_0001 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : TEnvFresh [((nb076_alpha_dummy_033), (nb076_alpha_dummy_036 m n)), ((nb076_alpha_dummy_032), (nb076_alpha_dummy_035 m n)), ((nb076_alpha_dummy_031), (nb076_alpha_dummy_034 m n)), ((nb076_alpha_dummy_029), (nb076_alpha_dummy_030 m n)), ((nb076_alpha_dummy_025), (nb076_alpha_dummy_027 m n)), ((nb076_alpha_dummy_026), (nb076_alpha_dummy_028 m n)), ((nb076_alpha_dummy_018), (nb076_alpha_dummy_020 m n)), ((nb076_alpha_dummy_017), (nb076_alpha_dummy_019 m n)), ((nb076_alpha_dummy_023), (nb076_alpha_dummy_024 m n)), ((nb076_alpha_dummy_021), (nb076_alpha_dummy_022 m n)), ((nb076_alpha_dummy_010), (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009), (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_015), (nb076_alpha_dummy_016 g m n a b)), ((nb076_alpha_dummy_013), (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb076_alpha_dummy_033) (nb076_alpha_dummy_036 m n) (nb076_wpp_notmem_0036) (nb076_wpp_notmem_0037 m n) (TEnvFresh.consFresh (nb076_alpha_dummy_032) (nb076_alpha_dummy_035 m n) (nb076_wpp_notmem_0038) (nb076_wpp_notmem_0039 m n) (TEnvFresh.consFresh (nb076_alpha_dummy_031) (nb076_alpha_dummy_034 m n) (nb076_wpp_notmem_0040) (nb076_wpp_notmem_0041 m n) (TEnvFresh.consFresh (nb076_alpha_dummy_029) (nb076_alpha_dummy_030 m n) (nb076_wpp_notmem_0042) (nb076_wpp_notmem_0043 m n) (TEnvFresh.consFresh (nb076_alpha_dummy_025) (nb076_alpha_dummy_027 m n) (nb076_wpp_notmem_0044) (nb076_wpp_notmem_0045 m n) (TEnvFresh.consFresh (nb076_alpha_dummy_026) (nb076_alpha_dummy_028 m n) (nb076_wpp_notmem_0046) (nb076_wpp_notmem_0047 m n) (TEnvFresh.consFresh (nb076_alpha_dummy_018) (nb076_alpha_dummy_020 m n) (nb076_wpp_notmem_0048) (nb076_wpp_notmem_0049 m n) (TEnvFresh.consFresh (nb076_alpha_dummy_017) (nb076_alpha_dummy_019 m n) (nb076_wpp_notmem_0050) (nb076_wpp_notmem_0051 m n) (TEnvFresh.consFresh (nb076_alpha_dummy_023) (nb076_alpha_dummy_024 m n) (nb076_wpp_notmem_0052) (nb076_wpp_notmem_0053 m n) (TEnvFresh.consFresh (nb076_alpha_dummy_021) (nb076_alpha_dummy_022 m n) (nb076_wpp_notmem_0054) (nb076_wpp_notmem_0055 m n) (TEnvFresh.consFresh (nb076_alpha_dummy_010) (nb076_alpha_dummy_012 g m n a b) (nb076_wpp_notmem_0056) (nb076_wpp_notmem_0057 g m n a b) (TEnvFresh.consFresh (nb076_alpha_dummy_009) (nb076_alpha_dummy_011 g m n a b) (nb076_wpp_notmem_0058) (nb076_wpp_notmem_0059 g m n a b) (TEnvFresh.consFresh (nb076_alpha_dummy_015) (nb076_alpha_dummy_016 g m n a b) (nb076_wpp_notmem_0060) (nb076_wpp_notmem_0061 g m n a b) (TEnvFresh.consFresh (nb076_alpha_dummy_013) (nb076_alpha_dummy_014 g m n a b) (nb076_wpp_notmem_0062) (nb076_wpp_notmem_0063 g m n a b) (TEnvFresh.consFresh (nb076_alpha_dummy_005) (nb076_alpha_dummy_006 g m n a b) (nb076_wpp_notmem_0064) (nb076_wpp_notmem_0065 g m n a b) (TEnvFresh.consFresh (nb076_alpha_dummy_004) n (nb076_wpp_notmem_0066) (nb076_wpp_notmem_0067 n) (TEnvFresh.consFresh (nb076_alpha_dummy_003) m (nb076_wpp_notmem_0068) (nb076_wpp_notmem_0069 m) (TEnvFresh.consFresh (nb076_alpha_dummy_007) (nb076_alpha_dummy_008 g m n a b) (nb076_wpp_notmem_0070) (nb076_wpp_notmem_0071 g m n a b) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))

noncomputable def nb076_wpp_refl_0001 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : TReflOn [((nb076_alpha_dummy_033), (nb076_alpha_dummy_036 m n)), ((nb076_alpha_dummy_032), (nb076_alpha_dummy_035 m n)), ((nb076_alpha_dummy_031), (nb076_alpha_dummy_034 m n)), ((nb076_alpha_dummy_029), (nb076_alpha_dummy_030 m n)), ((nb076_alpha_dummy_025), (nb076_alpha_dummy_027 m n)), ((nb076_alpha_dummy_026), (nb076_alpha_dummy_028 m n)), ((nb076_alpha_dummy_018), (nb076_alpha_dummy_020 m n)), ((nb076_alpha_dummy_017), (nb076_alpha_dummy_019 m n)), ((nb076_alpha_dummy_023), (nb076_alpha_dummy_024 m n)), ((nb076_alpha_dummy_021), (nb076_alpha_dummy_022 m n)), ((nb076_alpha_dummy_010), (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009), (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_015), (nb076_alpha_dummy_016 g m n a b)), ((nb076_alpha_dummy_013), (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb076_compact_envfresh_0001 g m n a b)

theorem nb076_wpp_notmem_0072 : (nb076_alpha_dummy_029) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_029, fv_syn_cnnc] using (nb076_compact_fv_empty_0006)

theorem nb076_wpp_notmem_0073 (m : Var) (n : Var) : (nb076_alpha_dummy_030 m n) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_030, fv_syn_cnnc] using (nb076_compact_fv_empty_0007 m n)

theorem nb076_wpp_notmem_0074 : (nb076_alpha_dummy_025) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_025, fv_syn_cnnc] using (nb076_compact_fv_empty_0008)

theorem nb076_wpp_notmem_0075 (m : Var) (n : Var) : (nb076_alpha_dummy_027 m n) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_027, fv_syn_cnnc] using (nb076_compact_fv_empty_0009 m n)

theorem nb076_wpp_notmem_0076 : (nb076_alpha_dummy_026) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_026, fv_syn_cnnc] using (nb076_compact_fv_empty_0010)

theorem nb076_wpp_notmem_0077 (m : Var) (n : Var) : (nb076_alpha_dummy_028 m n) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_028, fv_syn_cnnc] using (nb076_compact_fv_empty_0011 m n)

theorem nb076_wpp_notmem_0078 : (nb076_alpha_dummy_018) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_018, fv_syn_cnnc] using (nb076_compact_fv_empty_0012)

theorem nb076_wpp_notmem_0079 (m : Var) (n : Var) : (nb076_alpha_dummy_020 m n) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_020, fv_syn_cnnc] using (nb076_compact_fv_empty_0013 m n)

theorem nb076_wpp_notmem_0080 : (nb076_alpha_dummy_017) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_017, fv_syn_cnnc] using (nb076_compact_fv_empty_0014)

theorem nb076_wpp_notmem_0081 (m : Var) (n : Var) : (nb076_alpha_dummy_019 m n) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_019, fv_syn_cnnc] using (nb076_compact_fv_empty_0015 m n)

theorem nb076_wpp_notmem_0082 : (nb076_alpha_dummy_023) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_023, fv_syn_cnnc] using (nb076_compact_fv_empty_0016)

theorem nb076_wpp_notmem_0083 (m : Var) (n : Var) : (nb076_alpha_dummy_024 m n) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_024, fv_syn_cnnc] using (nb076_compact_fv_empty_0017 m n)

theorem nb076_wpp_notmem_0084 : (nb076_alpha_dummy_021) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_021, fv_syn_cnnc] using (nb076_compact_fv_empty_0018)

theorem nb076_wpp_notmem_0085 (m : Var) (n : Var) : (nb076_alpha_dummy_022 m n) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_022, fv_syn_cnnc] using (nb076_compact_fv_empty_0019 m n)

theorem nb076_wpp_notmem_0086 : (nb076_alpha_dummy_010) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_010, fv_syn_cnnc] using (nb076_compact_fv_empty_0020)

theorem nb076_wpp_notmem_0087 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_012 g m n a b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_012, fv_syn_cnnc] using (nb076_compact_fv_empty_0021 g m n a b)

theorem nb076_wpp_notmem_0088 : (nb076_alpha_dummy_009) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_009, fv_syn_cnnc] using (nb076_compact_fv_empty_0022)

theorem nb076_wpp_notmem_0089 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_011 g m n a b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_011, fv_syn_cnnc] using (nb076_compact_fv_empty_0023 g m n a b)

theorem nb076_wpp_notmem_0090 : (nb076_alpha_dummy_015) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_015, fv_syn_cnnc] using (nb076_compact_fv_empty_0024)

theorem nb076_wpp_notmem_0091 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_016 g m n a b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_016, fv_syn_cnnc] using (nb076_compact_fv_empty_0025 g m n a b)

theorem nb076_wpp_notmem_0092 : (nb076_alpha_dummy_013) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_013, fv_syn_cnnc] using (nb076_compact_fv_empty_0026)

theorem nb076_wpp_notmem_0093 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_014 g m n a b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_014, fv_syn_cnnc] using (nb076_compact_fv_empty_0027 g m n a b)

theorem nb076_wpp_notmem_0094 : (nb076_alpha_dummy_005) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_005, fv_syn_cnnc] using (nb076_compact_fv_empty_0028)

theorem nb076_wpp_notmem_0095 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_006 g m n a b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_006, fv_syn_cnnc] using (nb076_compact_fv_empty_0029 g m n a b)

theorem nb076_wpp_notmem_0096 : (nb076_alpha_dummy_004) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_004, fv_syn_cnnc] using (nb076_compact_fv_empty_0030)

theorem nb076_wpp_notmem_0097 (n : Var) : n ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb076_compact_fv_empty_0031 n)

theorem nb076_wpp_notmem_0098 : (nb076_alpha_dummy_003) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_003, fv_syn_cnnc] using (nb076_compact_fv_empty_0032)

theorem nb076_wpp_notmem_0099 (m : Var) : m ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb076_compact_fv_empty_0033 m)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
