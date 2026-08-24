import NAR4C056C001Part003

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

theorem nb056_fresh_251 (f : Var) : (nb056_alpha_dummy_198 f) ∉ (((syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))).fv) := by
  simpa only [nb056_alpha_dummy_198] using freshVar_not_mem (((syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))).fv) 0

theorem nb056_fresh_252 : (nb056_alpha_dummy_011) ∉ (({(nb056_alpha_dummy_005)} : Finset Var) ∪ ({(nb056_alpha_dummy_006)} : Finset Var) ∪ ((syn_wex (nb056_alpha_dummy_007) (syn_wa (syn_wbr (Class.cv (nb056_alpha_dummy_005)) (syn_ccnv (Class.cv (nb056_alpha_dummy_000))) (Class.cv (nb056_alpha_dummy_007))) (syn_wbr (Class.cv (nb056_alpha_dummy_007)) (Class.cv (nb056_alpha_dummy_000)) (Class.cv (nb056_alpha_dummy_006)))))).fv) := by
  simpa only [nb056_alpha_dummy_011] using freshVar_not_mem (({(nb056_alpha_dummy_005)} : Finset Var) ∪ ({(nb056_alpha_dummy_006)} : Finset Var) ∪ ((syn_wex (nb056_alpha_dummy_007) (syn_wa (syn_wbr (Class.cv (nb056_alpha_dummy_005)) (syn_ccnv (Class.cv (nb056_alpha_dummy_000))) (Class.cv (nb056_alpha_dummy_007))) (syn_wbr (Class.cv (nb056_alpha_dummy_007)) (Class.cv (nb056_alpha_dummy_000)) (Class.cv (nb056_alpha_dummy_006)))))).fv) 0

theorem nb056_fresh_253 (f : Var) : (nb056_alpha_dummy_012 f) ∉ (({(nb056_alpha_dummy_008 f)} : Finset Var) ∪ ({(nb056_alpha_dummy_009 f)} : Finset Var) ∪ ((syn_wex (nb056_alpha_dummy_010 f) (syn_wa (syn_wbr (Class.cv (nb056_alpha_dummy_008 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb056_alpha_dummy_010 f))) (syn_wbr (Class.cv (nb056_alpha_dummy_010 f)) (Class.cv f) (Class.cv (nb056_alpha_dummy_009 f)))))).fv) := by
  simpa only [nb056_alpha_dummy_012] using freshVar_not_mem (({(nb056_alpha_dummy_008 f)} : Finset Var) ∪ ({(nb056_alpha_dummy_009 f)} : Finset Var) ∪ ((syn_wex (nb056_alpha_dummy_010 f) (syn_wa (syn_wbr (Class.cv (nb056_alpha_dummy_008 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb056_alpha_dummy_010 f))) (syn_wbr (Class.cv (nb056_alpha_dummy_010 f)) (Class.cv f) (Class.cv (nb056_alpha_dummy_009 f)))))).fv) 0

theorem nb056_fresh_254 : (nb056_alpha_dummy_089) ∉ (({(nb056_alpha_dummy_085)} : Finset Var) ∪ ({(nb056_alpha_dummy_086)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb056_alpha_dummy_086)) (Class.cv (nb056_alpha_dummy_000)) (Class.cv (nb056_alpha_dummy_085)))).fv) := by
  simpa only [nb056_alpha_dummy_089] using freshVar_not_mem (({(nb056_alpha_dummy_085)} : Finset Var) ∪ ({(nb056_alpha_dummy_086)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb056_alpha_dummy_086)) (Class.cv (nb056_alpha_dummy_000)) (Class.cv (nb056_alpha_dummy_085)))).fv) 0

theorem nb056_fresh_255 (f : Var) : (nb056_alpha_dummy_090 f) ∉ (({(nb056_alpha_dummy_087 f)} : Finset Var) ∪ ({(nb056_alpha_dummy_088 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb056_alpha_dummy_088 f)) (Class.cv f) (Class.cv (nb056_alpha_dummy_087 f)))).fv) := by
  simpa only [nb056_alpha_dummy_090] using freshVar_not_mem (({(nb056_alpha_dummy_087 f)} : Finset Var) ∪ ({(nb056_alpha_dummy_088 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb056_alpha_dummy_088 f)) (Class.cv f) (Class.cv (nb056_alpha_dummy_087 f)))).fv) 0

theorem nb056_fresh_256 : (nb056_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb056_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb056_support_mem_0000 : (nb056_alpha_dummy_005) ∈ (({(nb056_alpha_dummy_005)} : Finset Var) ∪ ({(nb056_alpha_dummy_006)} : Finset Var) ∪ ((syn_wex (nb056_alpha_dummy_007) (syn_wa (syn_wbr (Class.cv (nb056_alpha_dummy_005)) (syn_ccnv (Class.cv (nb056_alpha_dummy_000))) (Class.cv (nb056_alpha_dummy_007))) (syn_wbr (Class.cv (nb056_alpha_dummy_007)) (Class.cv (nb056_alpha_dummy_000)) (Class.cv (nb056_alpha_dummy_006)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0001 (f : Var) : (nb056_alpha_dummy_008 f) ∈ (({(nb056_alpha_dummy_008 f)} : Finset Var) ∪ ({(nb056_alpha_dummy_009 f)} : Finset Var) ∪ ((syn_wex (nb056_alpha_dummy_010 f) (syn_wa (syn_wbr (Class.cv (nb056_alpha_dummy_008 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb056_alpha_dummy_010 f))) (syn_wbr (Class.cv (nb056_alpha_dummy_010 f)) (Class.cv f) (Class.cv (nb056_alpha_dummy_009 f)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0002 : (nb056_alpha_dummy_006) ∈ (({(nb056_alpha_dummy_005)} : Finset Var) ∪ ({(nb056_alpha_dummy_006)} : Finset Var) ∪ ((syn_wex (nb056_alpha_dummy_007) (syn_wa (syn_wbr (Class.cv (nb056_alpha_dummy_005)) (syn_ccnv (Class.cv (nb056_alpha_dummy_000))) (Class.cv (nb056_alpha_dummy_007))) (syn_wbr (Class.cv (nb056_alpha_dummy_007)) (Class.cv (nb056_alpha_dummy_000)) (Class.cv (nb056_alpha_dummy_006)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0003 (f : Var) : (nb056_alpha_dummy_009 f) ∈ (({(nb056_alpha_dummy_008 f)} : Finset Var) ∪ ({(nb056_alpha_dummy_009 f)} : Finset Var) ∪ ((syn_wex (nb056_alpha_dummy_010 f) (syn_wa (syn_wbr (Class.cv (nb056_alpha_dummy_008 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb056_alpha_dummy_010 f))) (syn_wbr (Class.cv (nb056_alpha_dummy_010 f)) (Class.cv f) (Class.cv (nb056_alpha_dummy_009 f)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0004 : (nb056_alpha_dummy_005) ∈ (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0005 : (nb056_alpha_dummy_005) ∈ (((syn_ccompl (Class.cab (nb056_alpha_dummy_013) (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_005)) (Wff.classEq (Class.cv (nb056_alpha_dummy_013)) (syn_cphi (Class.cv (nb056_alpha_dummy_014)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_013) (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_013)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0004) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0004) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0006 (f : Var) : (nb056_alpha_dummy_008 f) ∈ (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0007 (f : Var) : (nb056_alpha_dummy_008 f) ∈ (((syn_ccompl (Class.cab (nb056_alpha_dummy_015 f) (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_008 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_015 f) (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0006 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0006 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0008 : (nb056_alpha_dummy_005) ∈ (((Class.cab (nb056_alpha_dummy_013) (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_005)) (Wff.classEq (Class.cv (nb056_alpha_dummy_013)) (syn_cphi (Class.cv (nb056_alpha_dummy_014))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_013) (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_005)) (Wff.classEq (Class.cv (nb056_alpha_dummy_013)) (syn_cphi (Class.cv (nb056_alpha_dummy_014))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0004) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0004) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0009 (f : Var) : (nb056_alpha_dummy_008 f) ∈ (((Class.cab (nb056_alpha_dummy_015 f) (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_008 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_015 f) (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_008 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0006 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0006 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0010 : (nb056_alpha_dummy_014) ∈ (((Class.cv (nb056_alpha_dummy_014))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0011 (f : Var) : (nb056_alpha_dummy_016 f) ∈ (((Class.cv (nb056_alpha_dummy_016 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0012 : (nb056_alpha_dummy_021) ∈ (((Wff.classMem (Class.cv (nb056_alpha_dummy_021)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_021)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_021))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0013 (f : Var) : (nb056_alpha_dummy_023 f) ∈ (((Wff.classMem (Class.cv (nb056_alpha_dummy_023 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_023 f)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_023 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0014 : (nb056_alpha_dummy_021) ∈ (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0015 (f : Var) : (nb056_alpha_dummy_023 f) ∈ (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0016 : (nb056_alpha_dummy_028) ∈ (((syn_cnin (Class.cv (nb056_alpha_dummy_028)) (Class.cv (nb056_alpha_dummy_029)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_028)) (Class.cv (nb056_alpha_dummy_029)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0017 (f : Var) : (nb056_alpha_dummy_031 f) ∈ (((syn_cnin (Class.cv (nb056_alpha_dummy_031 f)) (Class.cv (nb056_alpha_dummy_032 f)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_031 f)) (Class.cv (nb056_alpha_dummy_032 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0018 : (nb056_alpha_dummy_028) ∈ (((Class.cv (nb056_alpha_dummy_028))).fv ∪ ((Class.cv (nb056_alpha_dummy_029))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0019 (f : Var) : (nb056_alpha_dummy_031 f) ∈ (((Class.cv (nb056_alpha_dummy_031 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_032 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0020 : (nb056_alpha_dummy_029) ∈ (((syn_cnin (Class.cv (nb056_alpha_dummy_028)) (Class.cv (nb056_alpha_dummy_029)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_028)) (Class.cv (nb056_alpha_dummy_029)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0021 (f : Var) : (nb056_alpha_dummy_032 f) ∈ (((syn_cnin (Class.cv (nb056_alpha_dummy_031 f)) (Class.cv (nb056_alpha_dummy_032 f)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_031 f)) (Class.cv (nb056_alpha_dummy_032 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0022 : (nb056_alpha_dummy_029) ∈ (((Class.cv (nb056_alpha_dummy_028))).fv ∪ ((Class.cv (nb056_alpha_dummy_029))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0023 (f : Var) : (nb056_alpha_dummy_032 f) ∈ (((Class.cv (nb056_alpha_dummy_031 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_032 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0024 : (nb056_alpha_dummy_028) ∈ (((syn_ccompl (Class.cv (nb056_alpha_dummy_028)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_029)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0025 (f : Var) : (nb056_alpha_dummy_031 f) ∈ (((syn_ccompl (Class.cv (nb056_alpha_dummy_031 f)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_032 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0026 : (nb056_alpha_dummy_028) ∈ (((Class.cv (nb056_alpha_dummy_028))).fv ∪ ((Class.cv (nb056_alpha_dummy_028))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0027 (f : Var) : (nb056_alpha_dummy_031 f) ∈ (((Class.cv (nb056_alpha_dummy_031 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_031 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0028 : (nb056_alpha_dummy_029) ∈ (((syn_ccompl (Class.cv (nb056_alpha_dummy_028)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_029)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0029 (f : Var) : (nb056_alpha_dummy_032 f) ∈ (((syn_ccompl (Class.cv (nb056_alpha_dummy_031 f)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_032 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0030 : (nb056_alpha_dummy_029) ∈ (((Class.cv (nb056_alpha_dummy_029))).fv ∪ ((Class.cv (nb056_alpha_dummy_029))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0031 (f : Var) : (nb056_alpha_dummy_032 f) ∈ (((Class.cv (nb056_alpha_dummy_032 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_032 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0032 : (nb056_alpha_dummy_006) ∈ (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0033 : (nb056_alpha_dummy_006) ∈ (((syn_ccompl (Class.cab (nb056_alpha_dummy_013) (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_005)) (Wff.classEq (Class.cv (nb056_alpha_dummy_013)) (syn_cphi (Class.cv (nb056_alpha_dummy_014)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_013) (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_013)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0032) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0032) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0034 (f : Var) : (nb056_alpha_dummy_009 f) ∈ (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0035 (f : Var) : (nb056_alpha_dummy_009 f) ∈ (((syn_ccompl (Class.cab (nb056_alpha_dummy_015 f) (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_008 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_015 f) (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0034 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0034 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0036 : (nb056_alpha_dummy_006) ∈ (((Class.cab (nb056_alpha_dummy_013) (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_013)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_013) (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_013)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0032) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0032) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0037 (f : Var) : (nb056_alpha_dummy_009 f) ∈ (((Class.cab (nb056_alpha_dummy_015 f) (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_015 f) (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0034 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0034 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0038 : (nb056_alpha_dummy_014) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_014))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0039 (f : Var) : (nb056_alpha_dummy_016 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0040 : (nb056_alpha_dummy_014) ∈ (((syn_cphi (Class.cv (nb056_alpha_dummy_014)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_014)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0041 (f : Var) : (nb056_alpha_dummy_016 f) ∈ (((syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0042 : (nb056_alpha_dummy_005) ∈ (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_007))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0043 : (nb056_alpha_dummy_005) ∈ (((syn_ccompl (Class.cab (nb056_alpha_dummy_049) (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_005)) (Wff.classEq (Class.cv (nb056_alpha_dummy_049)) (syn_cphi (Class.cv (nb056_alpha_dummy_050)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_049) (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_049)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0042) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0042) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0044 (f : Var) : (nb056_alpha_dummy_008 f) ∈ (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_010 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0045 (f : Var) : (nb056_alpha_dummy_008 f) ∈ (((syn_ccompl (Class.cab (nb056_alpha_dummy_051 f) (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_008 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_051 f) (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0044 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0044 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0046 : (nb056_alpha_dummy_005) ∈ (((Class.cab (nb056_alpha_dummy_049) (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_005)) (Wff.classEq (Class.cv (nb056_alpha_dummy_049)) (syn_cphi (Class.cv (nb056_alpha_dummy_050))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_049) (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_005)) (Wff.classEq (Class.cv (nb056_alpha_dummy_049)) (syn_cphi (Class.cv (nb056_alpha_dummy_050))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0042) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0042) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0047 (f : Var) : (nb056_alpha_dummy_008 f) ∈ (((Class.cab (nb056_alpha_dummy_051 f) (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_008 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_051 f) (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_008 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0044 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0044 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0048 : (nb056_alpha_dummy_050) ∈ (((Class.cv (nb056_alpha_dummy_050))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0049 (f : Var) : (nb056_alpha_dummy_052 f) ∈ (((Class.cv (nb056_alpha_dummy_052 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0050 : (nb056_alpha_dummy_057) ∈ (((Wff.classMem (Class.cv (nb056_alpha_dummy_057)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_057)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_057))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0051 (f : Var) : (nb056_alpha_dummy_059 f) ∈ (((Wff.classMem (Class.cv (nb056_alpha_dummy_059 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_059 f)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_059 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0052 : (nb056_alpha_dummy_057) ∈ (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0053 (f : Var) : (nb056_alpha_dummy_059 f) ∈ (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0054 : (nb056_alpha_dummy_064) ∈ (((syn_cnin (Class.cv (nb056_alpha_dummy_064)) (Class.cv (nb056_alpha_dummy_065)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_064)) (Class.cv (nb056_alpha_dummy_065)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0055 (f : Var) : (nb056_alpha_dummy_067 f) ∈ (((syn_cnin (Class.cv (nb056_alpha_dummy_067 f)) (Class.cv (nb056_alpha_dummy_068 f)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_067 f)) (Class.cv (nb056_alpha_dummy_068 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0056 : (nb056_alpha_dummy_064) ∈ (((Class.cv (nb056_alpha_dummy_064))).fv ∪ ((Class.cv (nb056_alpha_dummy_065))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0057 (f : Var) : (nb056_alpha_dummy_067 f) ∈ (((Class.cv (nb056_alpha_dummy_067 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_068 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0058 : (nb056_alpha_dummy_065) ∈ (((syn_cnin (Class.cv (nb056_alpha_dummy_064)) (Class.cv (nb056_alpha_dummy_065)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_064)) (Class.cv (nb056_alpha_dummy_065)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0059 (f : Var) : (nb056_alpha_dummy_068 f) ∈ (((syn_cnin (Class.cv (nb056_alpha_dummy_067 f)) (Class.cv (nb056_alpha_dummy_068 f)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_067 f)) (Class.cv (nb056_alpha_dummy_068 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0060 : (nb056_alpha_dummy_065) ∈ (((Class.cv (nb056_alpha_dummy_064))).fv ∪ ((Class.cv (nb056_alpha_dummy_065))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0061 (f : Var) : (nb056_alpha_dummy_068 f) ∈ (((Class.cv (nb056_alpha_dummy_067 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_068 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0062 : (nb056_alpha_dummy_064) ∈ (((syn_ccompl (Class.cv (nb056_alpha_dummy_064)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_065)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0063 (f : Var) : (nb056_alpha_dummy_067 f) ∈ (((syn_ccompl (Class.cv (nb056_alpha_dummy_067 f)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_068 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0064 : (nb056_alpha_dummy_064) ∈ (((Class.cv (nb056_alpha_dummy_064))).fv ∪ ((Class.cv (nb056_alpha_dummy_064))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0065 (f : Var) : (nb056_alpha_dummy_067 f) ∈ (((Class.cv (nb056_alpha_dummy_067 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_067 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0066 : (nb056_alpha_dummy_065) ∈ (((syn_ccompl (Class.cv (nb056_alpha_dummy_064)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_065)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0067 (f : Var) : (nb056_alpha_dummy_068 f) ∈ (((syn_ccompl (Class.cv (nb056_alpha_dummy_067 f)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_068 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0068 : (nb056_alpha_dummy_065) ∈ (((Class.cv (nb056_alpha_dummy_065))).fv ∪ ((Class.cv (nb056_alpha_dummy_065))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0069 (f : Var) : (nb056_alpha_dummy_068 f) ∈ (((Class.cv (nb056_alpha_dummy_068 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_068 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0070 : (nb056_alpha_dummy_007) ∈ (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_007))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0071 : (nb056_alpha_dummy_007) ∈ (((syn_ccompl (Class.cab (nb056_alpha_dummy_049) (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_005)) (Wff.classEq (Class.cv (nb056_alpha_dummy_049)) (syn_cphi (Class.cv (nb056_alpha_dummy_050)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_049) (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_049)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0070) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0070) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0072 (f : Var) : (nb056_alpha_dummy_010 f) ∈ (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_010 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0073 (f : Var) : (nb056_alpha_dummy_010 f) ∈ (((syn_ccompl (Class.cab (nb056_alpha_dummy_051 f) (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_008 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_051 f) (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0072 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0072 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0074 : (nb056_alpha_dummy_007) ∈ (((Class.cab (nb056_alpha_dummy_049) (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_049)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_049) (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_049)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0070) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0070) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0075 (f : Var) : (nb056_alpha_dummy_010 f) ∈ (((Class.cab (nb056_alpha_dummy_051 f) (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_051 f) (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0072 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0072 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0076 : (nb056_alpha_dummy_050) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_050))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0077 (f : Var) : (nb056_alpha_dummy_052 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0078 : (nb056_alpha_dummy_050) ∈ (((syn_cphi (Class.cv (nb056_alpha_dummy_050)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_050)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0079 (f : Var) : (nb056_alpha_dummy_052 f) ∈ (((syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0080 : (nb056_alpha_dummy_085) ∈ (({(nb056_alpha_dummy_085)} : Finset Var) ∪ ({(nb056_alpha_dummy_086)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb056_alpha_dummy_086)) (Class.cv (nb056_alpha_dummy_000)) (Class.cv (nb056_alpha_dummy_085)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0081 (f : Var) : (nb056_alpha_dummy_087 f) ∈ (({(nb056_alpha_dummy_087 f)} : Finset Var) ∪ ({(nb056_alpha_dummy_088 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb056_alpha_dummy_088 f)) (Class.cv f) (Class.cv (nb056_alpha_dummy_087 f)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0082 : (nb056_alpha_dummy_086) ∈ (({(nb056_alpha_dummy_085)} : Finset Var) ∪ ({(nb056_alpha_dummy_086)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb056_alpha_dummy_086)) (Class.cv (nb056_alpha_dummy_000)) (Class.cv (nb056_alpha_dummy_085)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0083 (f : Var) : (nb056_alpha_dummy_088 f) ∈ (({(nb056_alpha_dummy_087 f)} : Finset Var) ∪ ({(nb056_alpha_dummy_088 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb056_alpha_dummy_088 f)) (Class.cv f) (Class.cv (nb056_alpha_dummy_087 f)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0084 : (nb056_alpha_dummy_085) ∈ (((Class.cv (nb056_alpha_dummy_085))).fv ∪ ((Class.cv (nb056_alpha_dummy_086))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0085 : (nb056_alpha_dummy_085) ∈ (((syn_ccompl (Class.cab (nb056_alpha_dummy_091) (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_085)) (Wff.classEq (Class.cv (nb056_alpha_dummy_091)) (syn_cphi (Class.cv (nb056_alpha_dummy_092)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_091) (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086)) (Wff.classEq (Class.cv (nb056_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0084) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0084) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0086 (f : Var) : (nb056_alpha_dummy_087 f) ∈ (((Class.cv (nb056_alpha_dummy_087 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_088 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0087 (f : Var) : (nb056_alpha_dummy_087 f) ∈ (((syn_ccompl (Class.cab (nb056_alpha_dummy_093 f) (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_093 f) (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0086 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0086 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0088 : (nb056_alpha_dummy_085) ∈ (((Class.cab (nb056_alpha_dummy_091) (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_085)) (Wff.classEq (Class.cv (nb056_alpha_dummy_091)) (syn_cphi (Class.cv (nb056_alpha_dummy_092))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_091) (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_085)) (Wff.classEq (Class.cv (nb056_alpha_dummy_091)) (syn_cphi (Class.cv (nb056_alpha_dummy_092))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0084) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0084) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0089 (f : Var) : (nb056_alpha_dummy_087 f) ∈ (((Class.cab (nb056_alpha_dummy_093 f) (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_093 f) (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0086 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0086 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0090 : (nb056_alpha_dummy_092) ∈ (((Class.cv (nb056_alpha_dummy_092))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0091 (f : Var) : (nb056_alpha_dummy_094 f) ∈ (((Class.cv (nb056_alpha_dummy_094 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0092 : (nb056_alpha_dummy_099) ∈ (((Wff.classMem (Class.cv (nb056_alpha_dummy_099)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_099)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_099))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0093 (f : Var) : (nb056_alpha_dummy_101 f) ∈ (((Wff.classMem (Class.cv (nb056_alpha_dummy_101 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_101 f)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_101 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0094 : (nb056_alpha_dummy_099) ∈ (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0095 (f : Var) : (nb056_alpha_dummy_101 f) ∈ (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0096 : (nb056_alpha_dummy_106) ∈ (((syn_cnin (Class.cv (nb056_alpha_dummy_106)) (Class.cv (nb056_alpha_dummy_107)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_106)) (Class.cv (nb056_alpha_dummy_107)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0097 (f : Var) : (nb056_alpha_dummy_109 f) ∈ (((syn_cnin (Class.cv (nb056_alpha_dummy_109 f)) (Class.cv (nb056_alpha_dummy_110 f)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_109 f)) (Class.cv (nb056_alpha_dummy_110 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0098 : (nb056_alpha_dummy_106) ∈ (((Class.cv (nb056_alpha_dummy_106))).fv ∪ ((Class.cv (nb056_alpha_dummy_107))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0099 (f : Var) : (nb056_alpha_dummy_109 f) ∈ (((Class.cv (nb056_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_110 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0100 : (nb056_alpha_dummy_107) ∈ (((syn_cnin (Class.cv (nb056_alpha_dummy_106)) (Class.cv (nb056_alpha_dummy_107)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_106)) (Class.cv (nb056_alpha_dummy_107)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0101 (f : Var) : (nb056_alpha_dummy_110 f) ∈ (((syn_cnin (Class.cv (nb056_alpha_dummy_109 f)) (Class.cv (nb056_alpha_dummy_110 f)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_109 f)) (Class.cv (nb056_alpha_dummy_110 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0102 : (nb056_alpha_dummy_107) ∈ (((Class.cv (nb056_alpha_dummy_106))).fv ∪ ((Class.cv (nb056_alpha_dummy_107))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0103 (f : Var) : (nb056_alpha_dummy_110 f) ∈ (((Class.cv (nb056_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_110 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0104 : (nb056_alpha_dummy_106) ∈ (((syn_ccompl (Class.cv (nb056_alpha_dummy_106)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_107)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0105 (f : Var) : (nb056_alpha_dummy_109 f) ∈ (((syn_ccompl (Class.cv (nb056_alpha_dummy_109 f)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_110 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0106 : (nb056_alpha_dummy_106) ∈ (((Class.cv (nb056_alpha_dummy_106))).fv ∪ ((Class.cv (nb056_alpha_dummy_106))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0107 (f : Var) : (nb056_alpha_dummy_109 f) ∈ (((Class.cv (nb056_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_109 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0108 : (nb056_alpha_dummy_107) ∈ (((syn_ccompl (Class.cv (nb056_alpha_dummy_106)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_107)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0109 (f : Var) : (nb056_alpha_dummy_110 f) ∈ (((syn_ccompl (Class.cv (nb056_alpha_dummy_109 f)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_110 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0110 : (nb056_alpha_dummy_107) ∈ (((Class.cv (nb056_alpha_dummy_107))).fv ∪ ((Class.cv (nb056_alpha_dummy_107))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0111 (f : Var) : (nb056_alpha_dummy_110 f) ∈ (((Class.cv (nb056_alpha_dummy_110 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_110 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0112 : (nb056_alpha_dummy_086) ∈ (((Class.cv (nb056_alpha_dummy_085))).fv ∪ ((Class.cv (nb056_alpha_dummy_086))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0113 : (nb056_alpha_dummy_086) ∈ (((syn_ccompl (Class.cab (nb056_alpha_dummy_091) (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_085)) (Wff.classEq (Class.cv (nb056_alpha_dummy_091)) (syn_cphi (Class.cv (nb056_alpha_dummy_092)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_091) (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086)) (Wff.classEq (Class.cv (nb056_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0112) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0112) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0114 (f : Var) : (nb056_alpha_dummy_088 f) ∈ (((Class.cv (nb056_alpha_dummy_087 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_088 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0115 (f : Var) : (nb056_alpha_dummy_088 f) ∈ (((syn_ccompl (Class.cab (nb056_alpha_dummy_093 f) (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_093 f) (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0114 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0114 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0116 : (nb056_alpha_dummy_086) ∈ (((Class.cab (nb056_alpha_dummy_091) (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086)) (Wff.classEq (Class.cv (nb056_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_091) (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086)) (Wff.classEq (Class.cv (nb056_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0112) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0112) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0117 (f : Var) : (nb056_alpha_dummy_088 f) ∈ (((Class.cab (nb056_alpha_dummy_093 f) (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_093 f) (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0114 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0114 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0118 : (nb056_alpha_dummy_092) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_092))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0119 (f : Var) : (nb056_alpha_dummy_094 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0120 : (nb056_alpha_dummy_092) ∈ (((syn_cphi (Class.cv (nb056_alpha_dummy_092)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_092)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0121 (f : Var) : (nb056_alpha_dummy_094 f) ∈ (((syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0122 : (nb056_alpha_dummy_086) ∈ (((Class.cv (nb056_alpha_dummy_086))).fv ∪ ((Class.cv (nb056_alpha_dummy_085))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0123 : (nb056_alpha_dummy_086) ∈ (((syn_ccompl (Class.cab (nb056_alpha_dummy_127) (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_086)) (Wff.classEq (Class.cv (nb056_alpha_dummy_127)) (syn_cphi (Class.cv (nb056_alpha_dummy_128)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_127) (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085)) (Wff.classEq (Class.cv (nb056_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0122) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0122) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0124 (f : Var) : (nb056_alpha_dummy_088 f) ∈ (((Class.cv (nb056_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_087 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0125 (f : Var) : (nb056_alpha_dummy_088 f) ∈ (((syn_ccompl (Class.cab (nb056_alpha_dummy_129 f) (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_129 f) (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0124 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0124 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0126 : (nb056_alpha_dummy_086) ∈ (((Class.cab (nb056_alpha_dummy_127) (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_086)) (Wff.classEq (Class.cv (nb056_alpha_dummy_127)) (syn_cphi (Class.cv (nb056_alpha_dummy_128))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_127) (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_086)) (Wff.classEq (Class.cv (nb056_alpha_dummy_127)) (syn_cphi (Class.cv (nb056_alpha_dummy_128))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0122) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0122) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0127 (f : Var) : (nb056_alpha_dummy_088 f) ∈ (((Class.cab (nb056_alpha_dummy_129 f) (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_129 f) (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0124 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0124 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
