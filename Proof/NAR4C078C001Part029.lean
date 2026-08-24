import NAR4C078C001Part028

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

theorem nb078_support_mem_1017 (h : Var) : (nb078_alpha_dummy_975 h) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_975 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_975 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_975 h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1018 : (nb078_alpha_dummy_973) ∈ (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1019 (h : Var) : (nb078_alpha_dummy_975 h) ∈ (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1020 : (nb078_alpha_dummy_980) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_980)) (Class.cv (nb078_alpha_dummy_981)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_980)) (Class.cv (nb078_alpha_dummy_981)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1021 (h : Var) : (nb078_alpha_dummy_983 h) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_983 h)) (Class.cv (nb078_alpha_dummy_984 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_983 h)) (Class.cv (nb078_alpha_dummy_984 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1022 : (nb078_alpha_dummy_980) ∈ (((Class.cv (nb078_alpha_dummy_980))).fv ∪ ((Class.cv (nb078_alpha_dummy_981))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1023 (h : Var) : (nb078_alpha_dummy_983 h) ∈ (((Class.cv (nb078_alpha_dummy_983 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_984 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1024 : (nb078_alpha_dummy_981) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_980)) (Class.cv (nb078_alpha_dummy_981)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_980)) (Class.cv (nb078_alpha_dummy_981)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1025 (h : Var) : (nb078_alpha_dummy_984 h) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_983 h)) (Class.cv (nb078_alpha_dummy_984 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_983 h)) (Class.cv (nb078_alpha_dummy_984 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1026 : (nb078_alpha_dummy_981) ∈ (((Class.cv (nb078_alpha_dummy_980))).fv ∪ ((Class.cv (nb078_alpha_dummy_981))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1027 (h : Var) : (nb078_alpha_dummy_984 h) ∈ (((Class.cv (nb078_alpha_dummy_983 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_984 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1028 : (nb078_alpha_dummy_980) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_980)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_981)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1029 (h : Var) : (nb078_alpha_dummy_983 h) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_983 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_984 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1030 : (nb078_alpha_dummy_980) ∈ (((Class.cv (nb078_alpha_dummy_980))).fv ∪ ((Class.cv (nb078_alpha_dummy_980))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1031 (h : Var) : (nb078_alpha_dummy_983 h) ∈ (((Class.cv (nb078_alpha_dummy_983 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_983 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1032 : (nb078_alpha_dummy_981) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_980)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_981)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1033 (h : Var) : (nb078_alpha_dummy_984 h) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_983 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_984 h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1034 : (nb078_alpha_dummy_981) ∈ (((Class.cv (nb078_alpha_dummy_981))).fv ∪ ((Class.cv (nb078_alpha_dummy_981))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1035 (h : Var) : (nb078_alpha_dummy_984 h) ∈ (((Class.cv (nb078_alpha_dummy_984 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_984 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1036 : (nb078_alpha_dummy_961) ∈ (((Class.cv (nb078_alpha_dummy_962))).fv ∪ ((Class.cv (nb078_alpha_dummy_961))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1037 : (nb078_alpha_dummy_961) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_965) (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962)) (Wff.classEq (Class.cv (nb078_alpha_dummy_965)) (syn_cphi (Class.cv (nb078_alpha_dummy_966)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_965) (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961)) (Wff.classEq (Class.cv (nb078_alpha_dummy_965)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1036) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1036) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1038 (h : Var) : (nb078_alpha_dummy_963 h) ∈ (((Class.cv (nb078_alpha_dummy_964 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_963 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1039 (h : Var) : (nb078_alpha_dummy_963 h) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_967 h) (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_967 h) (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1038 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1038 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1040 : (nb078_alpha_dummy_961) ∈ (((Class.cab (nb078_alpha_dummy_965) (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961)) (Wff.classEq (Class.cv (nb078_alpha_dummy_965)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_965) (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961)) (Wff.classEq (Class.cv (nb078_alpha_dummy_965)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1036) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1036) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1041 (h : Var) : (nb078_alpha_dummy_963 h) ∈ (((Class.cab (nb078_alpha_dummy_967 h) (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_967 h) (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1038 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1038 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1042 : (nb078_alpha_dummy_966) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_966))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1043 (h : Var) : (nb078_alpha_dummy_968 h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1044 : (nb078_alpha_dummy_966) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_966)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_966)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1045 (h : Var) : (nb078_alpha_dummy_968 h) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1046 : (nb078_alpha_dummy_002) ∈ (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1047 (h : Var) : h ∈ (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1048 : (nb078_alpha_dummy_1006) ∈ (((Class.cv (nb078_alpha_dummy_1006))).fv ∪ ((Class.cv (nb078_alpha_dummy_1005))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1049 : (nb078_alpha_dummy_1006) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_1009) (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1009)) (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1009) (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1005)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1009)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1010))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1048) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1048) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1050 (h : Var) : (nb078_alpha_dummy_1008 h) ∈ (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1007 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1051 (h : Var) : (nb078_alpha_dummy_1008 h) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_1011 h) (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1011 h) (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1007 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1050 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1050 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1052 : (nb078_alpha_dummy_1006) ∈ (((Class.cab (nb078_alpha_dummy_1009) (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1009)) (syn_cphi (Class.cv (nb078_alpha_dummy_1010))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1009) (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1009)) (syn_cphi (Class.cv (nb078_alpha_dummy_1010))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1048) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1048) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1053 (h : Var) : (nb078_alpha_dummy_1008 h) ∈ (((Class.cab (nb078_alpha_dummy_1011 h) (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1011 h) (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1050 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1050 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1054 : (nb078_alpha_dummy_1010) ∈ (((Class.cv (nb078_alpha_dummy_1010))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1055 (h : Var) : (nb078_alpha_dummy_1012 h) ∈ (((Class.cv (nb078_alpha_dummy_1012 h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1056 : (nb078_alpha_dummy_1017) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_1017)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1017)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1017))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1057 (h : Var) : (nb078_alpha_dummy_1019 h) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_1019 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1019 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1019 h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1058 : (nb078_alpha_dummy_1017) ∈ (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1059 (h : Var) : (nb078_alpha_dummy_1019 h) ∈ (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1060 : (nb078_alpha_dummy_1024) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_1024)) (Class.cv (nb078_alpha_dummy_1025)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1024)) (Class.cv (nb078_alpha_dummy_1025)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1061 (h : Var) : (nb078_alpha_dummy_1027 h) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_1027 h)) (Class.cv (nb078_alpha_dummy_1028 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1027 h)) (Class.cv (nb078_alpha_dummy_1028 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1062 : (nb078_alpha_dummy_1024) ∈ (((Class.cv (nb078_alpha_dummy_1024))).fv ∪ ((Class.cv (nb078_alpha_dummy_1025))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1063 (h : Var) : (nb078_alpha_dummy_1027 h) ∈ (((Class.cv (nb078_alpha_dummy_1027 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1028 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1064 : (nb078_alpha_dummy_1025) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_1024)) (Class.cv (nb078_alpha_dummy_1025)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1024)) (Class.cv (nb078_alpha_dummy_1025)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1065 (h : Var) : (nb078_alpha_dummy_1028 h) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_1027 h)) (Class.cv (nb078_alpha_dummy_1028 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1027 h)) (Class.cv (nb078_alpha_dummy_1028 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1066 : (nb078_alpha_dummy_1025) ∈ (((Class.cv (nb078_alpha_dummy_1024))).fv ∪ ((Class.cv (nb078_alpha_dummy_1025))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1067 (h : Var) : (nb078_alpha_dummy_1028 h) ∈ (((Class.cv (nb078_alpha_dummy_1027 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1028 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1068 : (nb078_alpha_dummy_1024) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_1024)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_1025)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1069 (h : Var) : (nb078_alpha_dummy_1027 h) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_1027 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_1028 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1070 : (nb078_alpha_dummy_1024) ∈ (((Class.cv (nb078_alpha_dummy_1024))).fv ∪ ((Class.cv (nb078_alpha_dummy_1024))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1071 (h : Var) : (nb078_alpha_dummy_1027 h) ∈ (((Class.cv (nb078_alpha_dummy_1027 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1027 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1072 : (nb078_alpha_dummy_1025) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_1024)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_1025)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1073 (h : Var) : (nb078_alpha_dummy_1028 h) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_1027 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_1028 h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1074 : (nb078_alpha_dummy_1025) ∈ (((Class.cv (nb078_alpha_dummy_1025))).fv ∪ ((Class.cv (nb078_alpha_dummy_1025))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1075 (h : Var) : (nb078_alpha_dummy_1028 h) ∈ (((Class.cv (nb078_alpha_dummy_1028 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1028 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1076 : (nb078_alpha_dummy_1005) ∈ (((Class.cv (nb078_alpha_dummy_1006))).fv ∪ ((Class.cv (nb078_alpha_dummy_1005))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1077 : (nb078_alpha_dummy_1005) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_1009) (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1009)) (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1009) (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1005)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1009)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1010))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1076) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1076) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1078 (h : Var) : (nb078_alpha_dummy_1007 h) ∈ (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1007 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1079 (h : Var) : (nb078_alpha_dummy_1007 h) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_1011 h) (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1011 h) (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1007 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1078 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1078 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1080 : (nb078_alpha_dummy_1005) ∈ (((Class.cab (nb078_alpha_dummy_1009) (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1005)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1009)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1010))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1009) (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1005)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1009)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1010))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1076) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1076) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1081 (h : Var) : (nb078_alpha_dummy_1007 h) ∈ (((Class.cab (nb078_alpha_dummy_1011 h) (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1007 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1011 h) (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1007 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1078 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1078 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1082 : (nb078_alpha_dummy_1010) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1010))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1083 (h : Var) : (nb078_alpha_dummy_1012 h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1084 : (nb078_alpha_dummy_1010) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_1010)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1010)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1085 (h : Var) : (nb078_alpha_dummy_1012 h) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1086 : (nb078_alpha_dummy_002) ∈ (((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_004)))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_004)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1087 (y : Var) (h : Var) : h ∈ (((syn_cnin (syn_crn (Class.cv h)) (Class.cv y))).fv ∪ ((syn_cnin (syn_crn (Class.cv h)) (Class.cv y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1088 : (nb078_alpha_dummy_002) ∈ (((syn_crn (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((Class.cv (nb078_alpha_dummy_004))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1089 (y : Var) (h : Var) : h ∈ (((syn_crn (Class.cv h))).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1090 : (nb078_alpha_dummy_002) ∈ (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1091 (h : Var) : h ∈ (((Class.cv h)).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1092 : (nb078_alpha_dummy_004) ∈ (((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_004)))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_004)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1093 (y : Var) (h : Var) : y ∈ (((syn_cnin (syn_crn (Class.cv h)) (Class.cv y))).fv ∪ ((syn_cnin (syn_crn (Class.cv h)) (Class.cv y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1094 : (nb078_alpha_dummy_004) ∈ (((syn_crn (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((Class.cv (nb078_alpha_dummy_004))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1095 (y : Var) (h : Var) : y ∈ (((syn_crn (Class.cv h))).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1096 : (nb078_alpha_dummy_1049) ∈ (({(nb078_alpha_dummy_1049)} : Finset Var) ∪ ({(nb078_alpha_dummy_1050)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_1051) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_1049)) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))) (Class.cv (nb078_alpha_dummy_1051))) (syn_wbr (Class.cv (nb078_alpha_dummy_1051)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_1050)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1097 (h : Var) : (nb078_alpha_dummy_1052 h) ∈ (({(nb078_alpha_dummy_1052 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_1053 h)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_1054 h) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_1052 h)) (syn_ccnv (syn_ccnv (Class.cv h))) (Class.cv (nb078_alpha_dummy_1054 h))) (syn_wbr (Class.cv (nb078_alpha_dummy_1054 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb078_alpha_dummy_1053 h)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1098 : (nb078_alpha_dummy_1050) ∈ (({(nb078_alpha_dummy_1049)} : Finset Var) ∪ ({(nb078_alpha_dummy_1050)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_1051) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_1049)) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))) (Class.cv (nb078_alpha_dummy_1051))) (syn_wbr (Class.cv (nb078_alpha_dummy_1051)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_1050)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1099 (h : Var) : (nb078_alpha_dummy_1053 h) ∈ (({(nb078_alpha_dummy_1052 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_1053 h)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_1054 h) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_1052 h)) (syn_ccnv (syn_ccnv (Class.cv h))) (Class.cv (nb078_alpha_dummy_1054 h))) (syn_wbr (Class.cv (nb078_alpha_dummy_1054 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb078_alpha_dummy_1053 h)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1100 : (nb078_alpha_dummy_1049) ∈ (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1101 : (nb078_alpha_dummy_1049) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_1057) (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1057)) (syn_cphi (Class.cv (nb078_alpha_dummy_1058)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1057) (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1050)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1057)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1058))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1100) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1100) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1102 (h : Var) : (nb078_alpha_dummy_1052 h) ∈ (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1053 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1103 (h : Var) : (nb078_alpha_dummy_1052 h) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_1059 h) (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1059 h) (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1053 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1102 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1102 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1104 : (nb078_alpha_dummy_1049) ∈ (((Class.cab (nb078_alpha_dummy_1057) (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1057)) (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1057) (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1057)) (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1100) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1100) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1105 (h : Var) : (nb078_alpha_dummy_1052 h) ∈ (((Class.cab (nb078_alpha_dummy_1059 h) (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1059 h) (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1102 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1102 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1106 : (nb078_alpha_dummy_1058) ∈ (((Class.cv (nb078_alpha_dummy_1058))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1107 (h : Var) : (nb078_alpha_dummy_1060 h) ∈ (((Class.cv (nb078_alpha_dummy_1060 h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1108 : (nb078_alpha_dummy_1065) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_1065)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1065)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1065))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1109 (h : Var) : (nb078_alpha_dummy_1067 h) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_1067 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1067 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1067 h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1110 : (nb078_alpha_dummy_1065) ∈ (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1111 (h : Var) : (nb078_alpha_dummy_1067 h) ∈ (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1112 : (nb078_alpha_dummy_1072) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_1072)) (Class.cv (nb078_alpha_dummy_1073)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1072)) (Class.cv (nb078_alpha_dummy_1073)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1113 (h : Var) : (nb078_alpha_dummy_1075 h) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_1075 h)) (Class.cv (nb078_alpha_dummy_1076 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1075 h)) (Class.cv (nb078_alpha_dummy_1076 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1114 : (nb078_alpha_dummy_1072) ∈ (((Class.cv (nb078_alpha_dummy_1072))).fv ∪ ((Class.cv (nb078_alpha_dummy_1073))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1115 (h : Var) : (nb078_alpha_dummy_1075 h) ∈ (((Class.cv (nb078_alpha_dummy_1075 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1076 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1116 : (nb078_alpha_dummy_1073) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_1072)) (Class.cv (nb078_alpha_dummy_1073)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1072)) (Class.cv (nb078_alpha_dummy_1073)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1117 (h : Var) : (nb078_alpha_dummy_1076 h) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_1075 h)) (Class.cv (nb078_alpha_dummy_1076 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1075 h)) (Class.cv (nb078_alpha_dummy_1076 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1118 : (nb078_alpha_dummy_1073) ∈ (((Class.cv (nb078_alpha_dummy_1072))).fv ∪ ((Class.cv (nb078_alpha_dummy_1073))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1119 (h : Var) : (nb078_alpha_dummy_1076 h) ∈ (((Class.cv (nb078_alpha_dummy_1075 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1076 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1120 : (nb078_alpha_dummy_1072) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_1072)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_1073)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1121 (h : Var) : (nb078_alpha_dummy_1075 h) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_1075 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_1076 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1122 : (nb078_alpha_dummy_1072) ∈ (((Class.cv (nb078_alpha_dummy_1072))).fv ∪ ((Class.cv (nb078_alpha_dummy_1072))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1123 (h : Var) : (nb078_alpha_dummy_1075 h) ∈ (((Class.cv (nb078_alpha_dummy_1075 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1075 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1124 : (nb078_alpha_dummy_1073) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_1072)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_1073)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1125 (h : Var) : (nb078_alpha_dummy_1076 h) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_1075 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_1076 h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1126 : (nb078_alpha_dummy_1073) ∈ (((Class.cv (nb078_alpha_dummy_1073))).fv ∪ ((Class.cv (nb078_alpha_dummy_1073))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1127 (h : Var) : (nb078_alpha_dummy_1076 h) ∈ (((Class.cv (nb078_alpha_dummy_1076 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1076 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1128 : (nb078_alpha_dummy_1050) ∈ (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1129 : (nb078_alpha_dummy_1050) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_1057) (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1057)) (syn_cphi (Class.cv (nb078_alpha_dummy_1058)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1057) (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1050)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1057)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1058))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1128) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1128) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1130 (h : Var) : (nb078_alpha_dummy_1053 h) ∈ (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1053 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1131 (h : Var) : (nb078_alpha_dummy_1053 h) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_1059 h) (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1059 h) (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1053 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1130 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1130 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1132 : (nb078_alpha_dummy_1050) ∈ (((Class.cab (nb078_alpha_dummy_1057) (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1050)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1057)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1058))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1057) (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1050)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1057)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1058))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1128) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1128) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1133 (h : Var) : (nb078_alpha_dummy_1053 h) ∈ (((Class.cab (nb078_alpha_dummy_1059 h) (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1053 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1059 h) (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1053 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1130 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1130 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1134 : (nb078_alpha_dummy_1058) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1135 (h : Var) : (nb078_alpha_dummy_1060 h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1136 : (nb078_alpha_dummy_1058) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_1058)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1058)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1137 (h : Var) : (nb078_alpha_dummy_1060 h) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1138 : (nb078_alpha_dummy_1049) ∈ (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1051))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1139 : (nb078_alpha_dummy_1049) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_1093) (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1049)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1093)) (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1093) (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1051)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1093)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1094))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1138) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1138) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1140 (h : Var) : (nb078_alpha_dummy_1052 h) ∈ (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1054 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1141 (h : Var) : (nb078_alpha_dummy_1052 h) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_1095 h) (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1052 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1095 h) (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1054 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1140 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1140 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1142 : (nb078_alpha_dummy_1049) ∈ (((Class.cab (nb078_alpha_dummy_1093) (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1049)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1093)) (syn_cphi (Class.cv (nb078_alpha_dummy_1094))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1093) (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1049)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1093)) (syn_cphi (Class.cv (nb078_alpha_dummy_1094))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1138) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1138) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1143 (h : Var) : (nb078_alpha_dummy_1052 h) ∈ (((Class.cab (nb078_alpha_dummy_1095 h) (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1052 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1095 h) (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1052 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1140 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1140 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1144 : (nb078_alpha_dummy_1094) ∈ (((Class.cv (nb078_alpha_dummy_1094))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1145 (h : Var) : (nb078_alpha_dummy_1096 h) ∈ (((Class.cv (nb078_alpha_dummy_1096 h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1146 : (nb078_alpha_dummy_1101) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_1101)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1101)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1101))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1147 (h : Var) : (nb078_alpha_dummy_1103 h) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_1103 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1103 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1103 h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1148 : (nb078_alpha_dummy_1101) ∈ (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1149 (h : Var) : (nb078_alpha_dummy_1103 h) ∈ (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1150 : (nb078_alpha_dummy_1108) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_1108)) (Class.cv (nb078_alpha_dummy_1109)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1108)) (Class.cv (nb078_alpha_dummy_1109)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1151 (h : Var) : (nb078_alpha_dummy_1111 h) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_1111 h)) (Class.cv (nb078_alpha_dummy_1112 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1111 h)) (Class.cv (nb078_alpha_dummy_1112 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1152 : (nb078_alpha_dummy_1108) ∈ (((Class.cv (nb078_alpha_dummy_1108))).fv ∪ ((Class.cv (nb078_alpha_dummy_1109))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1153 (h : Var) : (nb078_alpha_dummy_1111 h) ∈ (((Class.cv (nb078_alpha_dummy_1111 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1112 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1154 : (nb078_alpha_dummy_1109) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_1108)) (Class.cv (nb078_alpha_dummy_1109)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1108)) (Class.cv (nb078_alpha_dummy_1109)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1155 (h : Var) : (nb078_alpha_dummy_1112 h) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_1111 h)) (Class.cv (nb078_alpha_dummy_1112 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1111 h)) (Class.cv (nb078_alpha_dummy_1112 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1156 : (nb078_alpha_dummy_1109) ∈ (((Class.cv (nb078_alpha_dummy_1108))).fv ∪ ((Class.cv (nb078_alpha_dummy_1109))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1157 (h : Var) : (nb078_alpha_dummy_1112 h) ∈ (((Class.cv (nb078_alpha_dummy_1111 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1112 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1158 : (nb078_alpha_dummy_1108) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_1108)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_1109)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1159 (h : Var) : (nb078_alpha_dummy_1111 h) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_1111 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_1112 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1160 : (nb078_alpha_dummy_1108) ∈ (((Class.cv (nb078_alpha_dummy_1108))).fv ∪ ((Class.cv (nb078_alpha_dummy_1108))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1161 (h : Var) : (nb078_alpha_dummy_1111 h) ∈ (((Class.cv (nb078_alpha_dummy_1111 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1111 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1162 : (nb078_alpha_dummy_1109) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_1108)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_1109)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1163 (h : Var) : (nb078_alpha_dummy_1112 h) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_1111 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_1112 h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1164 : (nb078_alpha_dummy_1109) ∈ (((Class.cv (nb078_alpha_dummy_1109))).fv ∪ ((Class.cv (nb078_alpha_dummy_1109))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
