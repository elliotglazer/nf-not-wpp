import NAR4C077C001Part006

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

theorem nb077_support_mem_0039 (F : Class) (I : Class) : (nb077_alpha_dummy_015 F I) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0038 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0038 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0040 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_017 x F I) ∈ (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_017 x F I))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0041 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_017 x F I) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_018 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_017 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0040 x F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0040 x F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0042 (F : Class) (I : Class) : (nb077_alpha_dummy_015 F I) ∈ (((Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0038 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0038 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0043 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_017 x F I) ∈ (((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_017 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_017 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0040 x F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0040 x F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0044 (F : Class) (I : Class) : (nb077_alpha_dummy_020 F I) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0045 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_022 x F I) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0046 (F : Class) (I : Class) : (nb077_alpha_dummy_020 F I) ∈ (((syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0047 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_022 x F I) ∈ (((syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0048 (F : Class) (I : Class) : (nb077_alpha_dummy_059 F I) ∈ (({(nb077_alpha_dummy_059 F I)} : Finset Var) ∪ ({(nb077_alpha_dummy_060 F I)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_061 F I) (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_059 F I)) (syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st)) (Class.cv (nb077_alpha_dummy_061 F I))) (syn_wbr (Class.cv (nb077_alpha_dummy_061 F I)) (syn_ccnv (syn_c1st)) (Class.cv (nb077_alpha_dummy_060 F I)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0049 (x : Var) : (nb077_alpha_dummy_062 x) ∈ (({(nb077_alpha_dummy_062 x)} : Finset Var) ∪ ({(nb077_alpha_dummy_063 x)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_064 x) (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_062 x)) (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st)) (Class.cv (nb077_alpha_dummy_064 x))) (syn_wbr (Class.cv (nb077_alpha_dummy_064 x)) (syn_ccnv (syn_c1st)) (Class.cv (nb077_alpha_dummy_063 x)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0050 (F : Class) (I : Class) : (nb077_alpha_dummy_060 F I) ∈ (({(nb077_alpha_dummy_059 F I)} : Finset Var) ∪ ({(nb077_alpha_dummy_060 F I)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_061 F I) (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_059 F I)) (syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st)) (Class.cv (nb077_alpha_dummy_061 F I))) (syn_wbr (Class.cv (nb077_alpha_dummy_061 F I)) (syn_ccnv (syn_c1st)) (Class.cv (nb077_alpha_dummy_060 F I)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0051 (x : Var) : (nb077_alpha_dummy_063 x) ∈ (({(nb077_alpha_dummy_062 x)} : Finset Var) ∪ ({(nb077_alpha_dummy_063 x)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_064 x) (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_062 x)) (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st)) (Class.cv (nb077_alpha_dummy_064 x))) (syn_wbr (Class.cv (nb077_alpha_dummy_064 x)) (syn_ccnv (syn_c1st)) (Class.cv (nb077_alpha_dummy_063 x)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0052 (F : Class) (I : Class) : (nb077_alpha_dummy_059 F I) ∈ (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_060 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0053 (F : Class) (I : Class) : (nb077_alpha_dummy_059 F I) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0052 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0052 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0054 (x : Var) : (nb077_alpha_dummy_062 x) ∈ (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0055 (x : Var) : (nb077_alpha_dummy_062 x) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0054 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0054 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0056 (F : Class) (I : Class) : (nb077_alpha_dummy_059 F I) ∈ (((Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0052 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0052 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0057 (x : Var) : (nb077_alpha_dummy_062 x) ∈ (((Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0054 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0054 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0058 (F : Class) (I : Class) : (nb077_alpha_dummy_068 F I) ∈ (((Class.cv (nb077_alpha_dummy_068 F I))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0059 (x : Var) : (nb077_alpha_dummy_070 x) ∈ (((Class.cv (nb077_alpha_dummy_070 x))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0060 (F : Class) (I : Class) : (nb077_alpha_dummy_075 F I) ∈ (((Wff.classMem (Class.cv (nb077_alpha_dummy_075 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_075 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_075 F I))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0061 (x : Var) : (nb077_alpha_dummy_077 x) ∈ (((Wff.classMem (Class.cv (nb077_alpha_dummy_077 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_077 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_077 x))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0062 (F : Class) (I : Class) : (nb077_alpha_dummy_075 F I) ∈ (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0063 (x : Var) : (nb077_alpha_dummy_077 x) ∈ (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0064 (F : Class) (I : Class) : (nb077_alpha_dummy_082 F I) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_082 F I)) (Class.cv (nb077_alpha_dummy_083 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_082 F I)) (Class.cv (nb077_alpha_dummy_083 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0065 (x : Var) : (nb077_alpha_dummy_085 x) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_085 x)) (Class.cv (nb077_alpha_dummy_086 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_085 x)) (Class.cv (nb077_alpha_dummy_086 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0066 (F : Class) (I : Class) : (nb077_alpha_dummy_082 F I) ∈ (((Class.cv (nb077_alpha_dummy_082 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_083 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0067 (x : Var) : (nb077_alpha_dummy_085 x) ∈ (((Class.cv (nb077_alpha_dummy_085 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_086 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0068 (F : Class) (I : Class) : (nb077_alpha_dummy_083 F I) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_082 F I)) (Class.cv (nb077_alpha_dummy_083 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_082 F I)) (Class.cv (nb077_alpha_dummy_083 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0069 (x : Var) : (nb077_alpha_dummy_086 x) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_085 x)) (Class.cv (nb077_alpha_dummy_086 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_085 x)) (Class.cv (nb077_alpha_dummy_086 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0070 (F : Class) (I : Class) : (nb077_alpha_dummy_083 F I) ∈ (((Class.cv (nb077_alpha_dummy_082 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_083 F I))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0071 (x : Var) : (nb077_alpha_dummy_086 x) ∈ (((Class.cv (nb077_alpha_dummy_085 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_086 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0072 (F : Class) (I : Class) : (nb077_alpha_dummy_082 F I) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_082 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_083 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0073 (x : Var) : (nb077_alpha_dummy_085 x) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_085 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_086 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0074 (F : Class) (I : Class) : (nb077_alpha_dummy_082 F I) ∈ (((Class.cv (nb077_alpha_dummy_082 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_082 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0075 (x : Var) : (nb077_alpha_dummy_085 x) ∈ (((Class.cv (nb077_alpha_dummy_085 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_085 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0076 (F : Class) (I : Class) : (nb077_alpha_dummy_083 F I) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_082 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_083 F I)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0077 (x : Var) : (nb077_alpha_dummy_086 x) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_085 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_086 x)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0078 (F : Class) (I : Class) : (nb077_alpha_dummy_083 F I) ∈ (((Class.cv (nb077_alpha_dummy_083 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_083 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0079 (x : Var) : (nb077_alpha_dummy_086 x) ∈ (((Class.cv (nb077_alpha_dummy_086 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_086 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0080 (F : Class) (I : Class) : (nb077_alpha_dummy_060 F I) ∈ (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_060 F I))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0081 (F : Class) (I : Class) : (nb077_alpha_dummy_060 F I) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0080 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0080 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0082 (x : Var) : (nb077_alpha_dummy_063 x) ∈ (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0083 (x : Var) : (nb077_alpha_dummy_063 x) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0082 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0082 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0084 (F : Class) (I : Class) : (nb077_alpha_dummy_060 F I) ∈ (((Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0080 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0080 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0085 (x : Var) : (nb077_alpha_dummy_063 x) ∈ (((Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0082 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0082 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0086 (F : Class) (I : Class) : (nb077_alpha_dummy_068 F I) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0087 (x : Var) : (nb077_alpha_dummy_070 x) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0088 (F : Class) (I : Class) : (nb077_alpha_dummy_068 F I) ∈ (((syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0089 (x : Var) : (nb077_alpha_dummy_070 x) ∈ (((syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0090 (F : Class) (I : Class) : (nb077_alpha_dummy_059 F I) ∈ (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_061 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0091 (F : Class) (I : Class) : (nb077_alpha_dummy_059 F I) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0090 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0090 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0092 (x : Var) : (nb077_alpha_dummy_062 x) ∈ (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_064 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0093 (x : Var) : (nb077_alpha_dummy_062 x) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0092 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0092 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0094 (F : Class) (I : Class) : (nb077_alpha_dummy_059 F I) ∈ (((Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0090 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0090 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0095 (x : Var) : (nb077_alpha_dummy_062 x) ∈ (((Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0092 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0092 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0096 (F : Class) (I : Class) : (nb077_alpha_dummy_104 F I) ∈ (((Class.cv (nb077_alpha_dummy_104 F I))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0097 (x : Var) : (nb077_alpha_dummy_106 x) ∈ (((Class.cv (nb077_alpha_dummy_106 x))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0098 (F : Class) (I : Class) : (nb077_alpha_dummy_111 F I) ∈ (((Wff.classMem (Class.cv (nb077_alpha_dummy_111 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_111 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_111 F I))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0099 (x : Var) : (nb077_alpha_dummy_113 x) ∈ (((Wff.classMem (Class.cv (nb077_alpha_dummy_113 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_113 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_113 x))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0100 (F : Class) (I : Class) : (nb077_alpha_dummy_111 F I) ∈ (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0101 (x : Var) : (nb077_alpha_dummy_113 x) ∈ (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0102 (F : Class) (I : Class) : (nb077_alpha_dummy_118 F I) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_118 F I)) (Class.cv (nb077_alpha_dummy_119 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_118 F I)) (Class.cv (nb077_alpha_dummy_119 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0103 (x : Var) : (nb077_alpha_dummy_121 x) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_121 x)) (Class.cv (nb077_alpha_dummy_122 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_121 x)) (Class.cv (nb077_alpha_dummy_122 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0104 (F : Class) (I : Class) : (nb077_alpha_dummy_118 F I) ∈ (((Class.cv (nb077_alpha_dummy_118 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_119 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0105 (x : Var) : (nb077_alpha_dummy_121 x) ∈ (((Class.cv (nb077_alpha_dummy_121 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_122 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0106 (F : Class) (I : Class) : (nb077_alpha_dummy_119 F I) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_118 F I)) (Class.cv (nb077_alpha_dummy_119 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_118 F I)) (Class.cv (nb077_alpha_dummy_119 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0107 (x : Var) : (nb077_alpha_dummy_122 x) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_121 x)) (Class.cv (nb077_alpha_dummy_122 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_121 x)) (Class.cv (nb077_alpha_dummy_122 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0108 (F : Class) (I : Class) : (nb077_alpha_dummy_119 F I) ∈ (((Class.cv (nb077_alpha_dummy_118 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_119 F I))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0109 (x : Var) : (nb077_alpha_dummy_122 x) ∈ (((Class.cv (nb077_alpha_dummy_121 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_122 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0110 (F : Class) (I : Class) : (nb077_alpha_dummy_118 F I) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_118 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_119 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0111 (x : Var) : (nb077_alpha_dummy_121 x) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_121 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_122 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0112 (F : Class) (I : Class) : (nb077_alpha_dummy_118 F I) ∈ (((Class.cv (nb077_alpha_dummy_118 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_118 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0113 (x : Var) : (nb077_alpha_dummy_121 x) ∈ (((Class.cv (nb077_alpha_dummy_121 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_121 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0114 (F : Class) (I : Class) : (nb077_alpha_dummy_119 F I) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_118 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_119 F I)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0115 (x : Var) : (nb077_alpha_dummy_122 x) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_121 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_122 x)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0116 (F : Class) (I : Class) : (nb077_alpha_dummy_119 F I) ∈ (((Class.cv (nb077_alpha_dummy_119 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_119 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0117 (x : Var) : (nb077_alpha_dummy_122 x) ∈ (((Class.cv (nb077_alpha_dummy_122 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_122 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0118 (F : Class) (I : Class) : (nb077_alpha_dummy_061 F I) ∈ (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_061 F I))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0119 (F : Class) (I : Class) : (nb077_alpha_dummy_061 F I) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0118 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0118 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0120 (x : Var) : (nb077_alpha_dummy_064 x) ∈ (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_064 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0121 (x : Var) : (nb077_alpha_dummy_064 x) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0120 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0120 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0122 (F : Class) (I : Class) : (nb077_alpha_dummy_061 F I) ∈ (((Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0118 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0118 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0123 (x : Var) : (nb077_alpha_dummy_064 x) ∈ (((Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0120 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0120 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0124 (F : Class) (I : Class) : (nb077_alpha_dummy_104 F I) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0125 (x : Var) : (nb077_alpha_dummy_106 x) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0126 (F : Class) (I : Class) : (nb077_alpha_dummy_104 F I) ∈ (((syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0127 (x : Var) : (nb077_alpha_dummy_106 x) ∈ (((syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0128 (F : Class) (I : Class) : (nb077_alpha_dummy_139 F I) ∈ (({(nb077_alpha_dummy_139 F I)} : Finset Var) ∪ ({(nb077_alpha_dummy_140 F I)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_141 F I) (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_139 F I)) (syn_c1st) (Class.cv (nb077_alpha_dummy_141 F I))) (syn_wbr (Class.cv (nb077_alpha_dummy_141 F I)) (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (Class.cv (nb077_alpha_dummy_140 F I)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0129 (x : Var) : (nb077_alpha_dummy_142 x) ∈ (({(nb077_alpha_dummy_142 x)} : Finset Var) ∪ ({(nb077_alpha_dummy_143 x)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_144 x) (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_142 x)) (syn_c1st) (Class.cv (nb077_alpha_dummy_144 x))) (syn_wbr (Class.cv (nb077_alpha_dummy_144 x)) (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (Class.cv (nb077_alpha_dummy_143 x)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0130 (F : Class) (I : Class) : (nb077_alpha_dummy_140 F I) ∈ (({(nb077_alpha_dummy_139 F I)} : Finset Var) ∪ ({(nb077_alpha_dummy_140 F I)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_141 F I) (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_139 F I)) (syn_c1st) (Class.cv (nb077_alpha_dummy_141 F I))) (syn_wbr (Class.cv (nb077_alpha_dummy_141 F I)) (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (Class.cv (nb077_alpha_dummy_140 F I)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0131 (x : Var) : (nb077_alpha_dummy_143 x) ∈ (({(nb077_alpha_dummy_142 x)} : Finset Var) ∪ ({(nb077_alpha_dummy_143 x)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_144 x) (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_142 x)) (syn_c1st) (Class.cv (nb077_alpha_dummy_144 x))) (syn_wbr (Class.cv (nb077_alpha_dummy_144 x)) (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (Class.cv (nb077_alpha_dummy_143 x)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0132 (F : Class) (I : Class) : (nb077_alpha_dummy_139 F I) ∈ (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_140 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0133 (F : Class) (I : Class) : (nb077_alpha_dummy_139 F I) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0132 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0132 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0134 (x : Var) : (nb077_alpha_dummy_142 x) ∈ (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0135 (x : Var) : (nb077_alpha_dummy_142 x) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0134 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0134 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0136 (F : Class) (I : Class) : (nb077_alpha_dummy_139 F I) ∈ (((Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0132 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0132 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0137 (x : Var) : (nb077_alpha_dummy_142 x) ∈ (((Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0134 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0134 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0138 (F : Class) (I : Class) : (nb077_alpha_dummy_148 F I) ∈ (((Class.cv (nb077_alpha_dummy_148 F I))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0139 (x : Var) : (nb077_alpha_dummy_150 x) ∈ (((Class.cv (nb077_alpha_dummy_150 x))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0140 (F : Class) (I : Class) : (nb077_alpha_dummy_155 F I) ∈ (((Wff.classMem (Class.cv (nb077_alpha_dummy_155 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_155 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_155 F I))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0141 (x : Var) : (nb077_alpha_dummy_157 x) ∈ (((Wff.classMem (Class.cv (nb077_alpha_dummy_157 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_157 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_157 x))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0142 (F : Class) (I : Class) : (nb077_alpha_dummy_155 F I) ∈ (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0143 (x : Var) : (nb077_alpha_dummy_157 x) ∈ (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0144 (F : Class) (I : Class) : (nb077_alpha_dummy_162 F I) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_162 F I)) (Class.cv (nb077_alpha_dummy_163 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_162 F I)) (Class.cv (nb077_alpha_dummy_163 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0145 (x : Var) : (nb077_alpha_dummy_165 x) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_165 x)) (Class.cv (nb077_alpha_dummy_166 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_165 x)) (Class.cv (nb077_alpha_dummy_166 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0146 (F : Class) (I : Class) : (nb077_alpha_dummy_162 F I) ∈ (((Class.cv (nb077_alpha_dummy_162 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_163 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0147 (x : Var) : (nb077_alpha_dummy_165 x) ∈ (((Class.cv (nb077_alpha_dummy_165 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_166 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0148 (F : Class) (I : Class) : (nb077_alpha_dummy_163 F I) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_162 F I)) (Class.cv (nb077_alpha_dummy_163 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_162 F I)) (Class.cv (nb077_alpha_dummy_163 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0149 (x : Var) : (nb077_alpha_dummy_166 x) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_165 x)) (Class.cv (nb077_alpha_dummy_166 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_165 x)) (Class.cv (nb077_alpha_dummy_166 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0150 (F : Class) (I : Class) : (nb077_alpha_dummy_163 F I) ∈ (((Class.cv (nb077_alpha_dummy_162 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_163 F I))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0151 (x : Var) : (nb077_alpha_dummy_166 x) ∈ (((Class.cv (nb077_alpha_dummy_165 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_166 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0152 (F : Class) (I : Class) : (nb077_alpha_dummy_162 F I) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_162 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_163 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0153 (x : Var) : (nb077_alpha_dummy_165 x) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_165 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_166 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0154 (F : Class) (I : Class) : (nb077_alpha_dummy_162 F I) ∈ (((Class.cv (nb077_alpha_dummy_162 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_162 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0155 (x : Var) : (nb077_alpha_dummy_165 x) ∈ (((Class.cv (nb077_alpha_dummy_165 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_165 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0156 (F : Class) (I : Class) : (nb077_alpha_dummy_163 F I) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_162 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_163 F I)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0157 (x : Var) : (nb077_alpha_dummy_166 x) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_165 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_166 x)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0158 (F : Class) (I : Class) : (nb077_alpha_dummy_163 F I) ∈ (((Class.cv (nb077_alpha_dummy_163 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_163 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0159 (x : Var) : (nb077_alpha_dummy_166 x) ∈ (((Class.cv (nb077_alpha_dummy_166 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_166 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0160 (F : Class) (I : Class) : (nb077_alpha_dummy_140 F I) ∈ (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_140 F I))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0161 (F : Class) (I : Class) : (nb077_alpha_dummy_140 F I) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0160 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0160 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0162 (x : Var) : (nb077_alpha_dummy_143 x) ∈ (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0163 (x : Var) : (nb077_alpha_dummy_143 x) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0162 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0162 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0164 (F : Class) (I : Class) : (nb077_alpha_dummy_140 F I) ∈ (((Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0160 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0160 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
