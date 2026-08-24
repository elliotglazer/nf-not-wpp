import NAR4C078C001Part027

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

theorem nb078_support_mem_0878 : (nb078_alpha_dummy_847) ∈ (({(nb078_alpha_dummy_847)} : Finset Var) ∪ ({(nb078_alpha_dummy_848)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_848)) (Class.cv (nb078_alpha_dummy_002)) (Class.cv (nb078_alpha_dummy_847)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0879 (h : Var) : (nb078_alpha_dummy_849 h) ∈ (({(nb078_alpha_dummy_849 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_850 h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_850 h)) (Class.cv h) (Class.cv (nb078_alpha_dummy_849 h)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0880 : (nb078_alpha_dummy_848) ∈ (({(nb078_alpha_dummy_847)} : Finset Var) ∪ ({(nb078_alpha_dummy_848)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_848)) (Class.cv (nb078_alpha_dummy_002)) (Class.cv (nb078_alpha_dummy_847)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0881 (h : Var) : (nb078_alpha_dummy_850 h) ∈ (({(nb078_alpha_dummy_849 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_850 h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_850 h)) (Class.cv h) (Class.cv (nb078_alpha_dummy_849 h)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0882 : (nb078_alpha_dummy_847) ∈ (((Class.cv (nb078_alpha_dummy_847))).fv ∪ ((Class.cv (nb078_alpha_dummy_848))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0883 : (nb078_alpha_dummy_847) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_853) (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847)) (Wff.classEq (Class.cv (nb078_alpha_dummy_853)) (syn_cphi (Class.cv (nb078_alpha_dummy_854)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_853) (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_848)) (Wff.classEq (Class.cv (nb078_alpha_dummy_853)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_854))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0882) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0882) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0884 (h : Var) : (nb078_alpha_dummy_849 h) ∈ (((Class.cv (nb078_alpha_dummy_849 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_850 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0885 (h : Var) : (nb078_alpha_dummy_849 h) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_855 h) (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_855 h) (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_850 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0884 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0884 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0886 : (nb078_alpha_dummy_847) ∈ (((Class.cab (nb078_alpha_dummy_853) (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847)) (Wff.classEq (Class.cv (nb078_alpha_dummy_853)) (syn_cphi (Class.cv (nb078_alpha_dummy_854))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_853) (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847)) (Wff.classEq (Class.cv (nb078_alpha_dummy_853)) (syn_cphi (Class.cv (nb078_alpha_dummy_854))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0882) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0882) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0887 (h : Var) : (nb078_alpha_dummy_849 h) ∈ (((Class.cab (nb078_alpha_dummy_855 h) (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_855 h) (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0884 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0884 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0888 : (nb078_alpha_dummy_854) ∈ (((Class.cv (nb078_alpha_dummy_854))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0889 (h : Var) : (nb078_alpha_dummy_856 h) ∈ (((Class.cv (nb078_alpha_dummy_856 h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0890 : (nb078_alpha_dummy_861) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_861)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_861)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_861))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0891 (h : Var) : (nb078_alpha_dummy_863 h) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_863 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_863 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_863 h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0892 : (nb078_alpha_dummy_861) ∈ (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0893 (h : Var) : (nb078_alpha_dummy_863 h) ∈ (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0894 : (nb078_alpha_dummy_868) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_868)) (Class.cv (nb078_alpha_dummy_869)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_868)) (Class.cv (nb078_alpha_dummy_869)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0895 (h : Var) : (nb078_alpha_dummy_871 h) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_871 h)) (Class.cv (nb078_alpha_dummy_872 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_871 h)) (Class.cv (nb078_alpha_dummy_872 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0896 : (nb078_alpha_dummy_868) ∈ (((Class.cv (nb078_alpha_dummy_868))).fv ∪ ((Class.cv (nb078_alpha_dummy_869))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0897 (h : Var) : (nb078_alpha_dummy_871 h) ∈ (((Class.cv (nb078_alpha_dummy_871 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_872 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0898 : (nb078_alpha_dummy_869) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_868)) (Class.cv (nb078_alpha_dummy_869)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_868)) (Class.cv (nb078_alpha_dummy_869)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0899 (h : Var) : (nb078_alpha_dummy_872 h) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_871 h)) (Class.cv (nb078_alpha_dummy_872 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_871 h)) (Class.cv (nb078_alpha_dummy_872 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0900 : (nb078_alpha_dummy_869) ∈ (((Class.cv (nb078_alpha_dummy_868))).fv ∪ ((Class.cv (nb078_alpha_dummy_869))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0901 (h : Var) : (nb078_alpha_dummy_872 h) ∈ (((Class.cv (nb078_alpha_dummy_871 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_872 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0902 : (nb078_alpha_dummy_868) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_868)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_869)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0903 (h : Var) : (nb078_alpha_dummy_871 h) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_871 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_872 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0904 : (nb078_alpha_dummy_868) ∈ (((Class.cv (nb078_alpha_dummy_868))).fv ∪ ((Class.cv (nb078_alpha_dummy_868))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0905 (h : Var) : (nb078_alpha_dummy_871 h) ∈ (((Class.cv (nb078_alpha_dummy_871 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_871 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0906 : (nb078_alpha_dummy_869) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_868)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_869)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0907 (h : Var) : (nb078_alpha_dummy_872 h) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_871 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_872 h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0908 : (nb078_alpha_dummy_869) ∈ (((Class.cv (nb078_alpha_dummy_869))).fv ∪ ((Class.cv (nb078_alpha_dummy_869))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0909 (h : Var) : (nb078_alpha_dummy_872 h) ∈ (((Class.cv (nb078_alpha_dummy_872 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_872 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0910 : (nb078_alpha_dummy_848) ∈ (((Class.cv (nb078_alpha_dummy_847))).fv ∪ ((Class.cv (nb078_alpha_dummy_848))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0911 : (nb078_alpha_dummy_848) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_853) (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847)) (Wff.classEq (Class.cv (nb078_alpha_dummy_853)) (syn_cphi (Class.cv (nb078_alpha_dummy_854)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_853) (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_848)) (Wff.classEq (Class.cv (nb078_alpha_dummy_853)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_854))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0910) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0910) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0912 (h : Var) : (nb078_alpha_dummy_850 h) ∈ (((Class.cv (nb078_alpha_dummy_849 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_850 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0913 (h : Var) : (nb078_alpha_dummy_850 h) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_855 h) (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_855 h) (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_850 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0912 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0912 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0914 : (nb078_alpha_dummy_848) ∈ (((Class.cab (nb078_alpha_dummy_853) (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_848)) (Wff.classEq (Class.cv (nb078_alpha_dummy_853)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_854))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_853) (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_848)) (Wff.classEq (Class.cv (nb078_alpha_dummy_853)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_854))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0910) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0910) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0915 (h : Var) : (nb078_alpha_dummy_850 h) ∈ (((Class.cab (nb078_alpha_dummy_855 h) (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_850 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_855 h) (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_850 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0912 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0912 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0916 : (nb078_alpha_dummy_854) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_854))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0917 (h : Var) : (nb078_alpha_dummy_856 h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0918 : (nb078_alpha_dummy_854) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_854)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_854)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0919 (h : Var) : (nb078_alpha_dummy_856 h) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0920 : (nb078_alpha_dummy_848) ∈ (((Class.cv (nb078_alpha_dummy_848))).fv ∪ ((Class.cv (nb078_alpha_dummy_847))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0921 : (nb078_alpha_dummy_848) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_889) (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848)) (Wff.classEq (Class.cv (nb078_alpha_dummy_889)) (syn_cphi (Class.cv (nb078_alpha_dummy_890)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_889) (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_847)) (Wff.classEq (Class.cv (nb078_alpha_dummy_889)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_890))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0920) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0920) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0922 (h : Var) : (nb078_alpha_dummy_850 h) ∈ (((Class.cv (nb078_alpha_dummy_850 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_849 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0923 (h : Var) : (nb078_alpha_dummy_850 h) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_891 h) (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_891 h) (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_849 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0922 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0922 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0924 : (nb078_alpha_dummy_848) ∈ (((Class.cab (nb078_alpha_dummy_889) (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848)) (Wff.classEq (Class.cv (nb078_alpha_dummy_889)) (syn_cphi (Class.cv (nb078_alpha_dummy_890))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_889) (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848)) (Wff.classEq (Class.cv (nb078_alpha_dummy_889)) (syn_cphi (Class.cv (nb078_alpha_dummy_890))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0920) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0920) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0925 (h : Var) : (nb078_alpha_dummy_850 h) ∈ (((Class.cab (nb078_alpha_dummy_891 h) (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_891 h) (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0922 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0922 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0926 : (nb078_alpha_dummy_890) ∈ (((Class.cv (nb078_alpha_dummy_890))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0927 (h : Var) : (nb078_alpha_dummy_892 h) ∈ (((Class.cv (nb078_alpha_dummy_892 h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0928 : (nb078_alpha_dummy_897) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_897)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_897)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_897))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0929 (h : Var) : (nb078_alpha_dummy_899 h) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_899 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_899 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_899 h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0930 : (nb078_alpha_dummy_897) ∈ (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0931 (h : Var) : (nb078_alpha_dummy_899 h) ∈ (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0932 : (nb078_alpha_dummy_904) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_904)) (Class.cv (nb078_alpha_dummy_905)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_904)) (Class.cv (nb078_alpha_dummy_905)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0933 (h : Var) : (nb078_alpha_dummy_907 h) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_907 h)) (Class.cv (nb078_alpha_dummy_908 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_907 h)) (Class.cv (nb078_alpha_dummy_908 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0934 : (nb078_alpha_dummy_904) ∈ (((Class.cv (nb078_alpha_dummy_904))).fv ∪ ((Class.cv (nb078_alpha_dummy_905))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0935 (h : Var) : (nb078_alpha_dummy_907 h) ∈ (((Class.cv (nb078_alpha_dummy_907 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_908 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0936 : (nb078_alpha_dummy_905) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_904)) (Class.cv (nb078_alpha_dummy_905)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_904)) (Class.cv (nb078_alpha_dummy_905)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0937 (h : Var) : (nb078_alpha_dummy_908 h) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_907 h)) (Class.cv (nb078_alpha_dummy_908 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_907 h)) (Class.cv (nb078_alpha_dummy_908 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0938 : (nb078_alpha_dummy_905) ∈ (((Class.cv (nb078_alpha_dummy_904))).fv ∪ ((Class.cv (nb078_alpha_dummy_905))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0939 (h : Var) : (nb078_alpha_dummy_908 h) ∈ (((Class.cv (nb078_alpha_dummy_907 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_908 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0940 : (nb078_alpha_dummy_904) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_904)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_905)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0941 (h : Var) : (nb078_alpha_dummy_907 h) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_907 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_908 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0942 : (nb078_alpha_dummy_904) ∈ (((Class.cv (nb078_alpha_dummy_904))).fv ∪ ((Class.cv (nb078_alpha_dummy_904))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0943 (h : Var) : (nb078_alpha_dummy_907 h) ∈ (((Class.cv (nb078_alpha_dummy_907 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_907 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0944 : (nb078_alpha_dummy_905) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_904)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_905)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0945 (h : Var) : (nb078_alpha_dummy_908 h) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_907 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_908 h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0946 : (nb078_alpha_dummy_905) ∈ (((Class.cv (nb078_alpha_dummy_905))).fv ∪ ((Class.cv (nb078_alpha_dummy_905))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0947 (h : Var) : (nb078_alpha_dummy_908 h) ∈ (((Class.cv (nb078_alpha_dummy_908 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_908 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0948 : (nb078_alpha_dummy_847) ∈ (((Class.cv (nb078_alpha_dummy_848))).fv ∪ ((Class.cv (nb078_alpha_dummy_847))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0949 : (nb078_alpha_dummy_847) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_889) (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848)) (Wff.classEq (Class.cv (nb078_alpha_dummy_889)) (syn_cphi (Class.cv (nb078_alpha_dummy_890)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_889) (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_847)) (Wff.classEq (Class.cv (nb078_alpha_dummy_889)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_890))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0948) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0948) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0950 (h : Var) : (nb078_alpha_dummy_849 h) ∈ (((Class.cv (nb078_alpha_dummy_850 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_849 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0951 (h : Var) : (nb078_alpha_dummy_849 h) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_891 h) (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_891 h) (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_849 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0950 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0950 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0952 : (nb078_alpha_dummy_847) ∈ (((Class.cab (nb078_alpha_dummy_889) (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_847)) (Wff.classEq (Class.cv (nb078_alpha_dummy_889)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_890))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_889) (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_847)) (Wff.classEq (Class.cv (nb078_alpha_dummy_889)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_890))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0948) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0948) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0953 (h : Var) : (nb078_alpha_dummy_849 h) ∈ (((Class.cab (nb078_alpha_dummy_891 h) (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_849 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_891 h) (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_849 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0950 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0950 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0954 : (nb078_alpha_dummy_890) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_890))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0955 (h : Var) : (nb078_alpha_dummy_892 h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0956 : (nb078_alpha_dummy_890) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_890)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_890)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0957 (h : Var) : (nb078_alpha_dummy_892 h) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0958 : (nb078_alpha_dummy_002) ∈ (((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_002)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_002)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))) (syn_cid))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0959 (h : Var) : h ∈ (((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0960 : (nb078_alpha_dummy_002) ∈ (((syn_ccom (Class.cv (nb078_alpha_dummy_002)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv ∪ ((syn_cid)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0961 (h : Var) : h ∈ (((syn_ccom (Class.cv h) (syn_ccnv (Class.cv h)))).fv ∪ ((syn_cid)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0962 : (nb078_alpha_dummy_002) ∈ (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0963 : (nb078_alpha_dummy_002) ∈ (({(nb078_alpha_dummy_767)} : Finset Var) ∪ ({(nb078_alpha_dummy_768)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_769) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_767)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_769))) (syn_wbr (Class.cv (nb078_alpha_dummy_769)) (Class.cv (nb078_alpha_dummy_002)) (Class.cv (nb078_alpha_dummy_768)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0962) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_left
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb078_support_mem_0964 (h : Var) : h ∈ (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0965 (h : Var) : h ∈ (({(nb078_alpha_dummy_770 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_771 h)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_772 h) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_770 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb078_alpha_dummy_772 h))) (syn_wbr (Class.cv (nb078_alpha_dummy_772 h)) (Class.cv h) (Class.cv (nb078_alpha_dummy_771 h)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0964 h) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_left
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb078_support_mem_0966 : (nb078_alpha_dummy_002) ∈ (({(nb078_alpha_dummy_847)} : Finset Var) ∪ ({(nb078_alpha_dummy_848)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_848)) (Class.cv (nb078_alpha_dummy_002)) (Class.cv (nb078_alpha_dummy_847)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0967 (h : Var) : h ∈ (({(nb078_alpha_dummy_849 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_850 h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_850 h)) (Class.cv h) (Class.cv (nb078_alpha_dummy_849 h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0968 : (nb078_alpha_dummy_002) ∈ (((Class.cv (nb078_alpha_dummy_002))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0969 (h : Var) : h ∈ (((Class.cv h)).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0970 : (nb078_alpha_dummy_769) ∈ (((Class.cv (nb078_alpha_dummy_769))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0971 : (nb078_alpha_dummy_769) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_925) (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769)) (Wff.classEq (Class.cv (nb078_alpha_dummy_925)) (syn_cphi (Class.cv (nb078_alpha_dummy_926)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_925) (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_768)) (Wff.classEq (Class.cv (nb078_alpha_dummy_925)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_926))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0970) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0970) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0972 (h : Var) : (nb078_alpha_dummy_772 h) ∈ (((Class.cv (nb078_alpha_dummy_772 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0973 (h : Var) : (nb078_alpha_dummy_772 h) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_927 h) (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_927 h) (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_771 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0972 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0972 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0974 : (nb078_alpha_dummy_769) ∈ (((Class.cab (nb078_alpha_dummy_925) (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769)) (Wff.classEq (Class.cv (nb078_alpha_dummy_925)) (syn_cphi (Class.cv (nb078_alpha_dummy_926))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_925) (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769)) (Wff.classEq (Class.cv (nb078_alpha_dummy_925)) (syn_cphi (Class.cv (nb078_alpha_dummy_926))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0970) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0970) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0975 (h : Var) : (nb078_alpha_dummy_772 h) ∈ (((Class.cab (nb078_alpha_dummy_927 h) (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_927 h) (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0972 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0972 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0976 : (nb078_alpha_dummy_926) ∈ (((Class.cv (nb078_alpha_dummy_926))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0977 (h : Var) : (nb078_alpha_dummy_928 h) ∈ (((Class.cv (nb078_alpha_dummy_928 h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0978 : (nb078_alpha_dummy_933) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_933)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_933)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_933))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0979 (h : Var) : (nb078_alpha_dummy_935 h) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_935 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_935 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_935 h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0980 : (nb078_alpha_dummy_933) ∈ (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0981 (h : Var) : (nb078_alpha_dummy_935 h) ∈ (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0982 : (nb078_alpha_dummy_940) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_940)) (Class.cv (nb078_alpha_dummy_941)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_940)) (Class.cv (nb078_alpha_dummy_941)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0983 (h : Var) : (nb078_alpha_dummy_943 h) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_943 h)) (Class.cv (nb078_alpha_dummy_944 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_943 h)) (Class.cv (nb078_alpha_dummy_944 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0984 : (nb078_alpha_dummy_940) ∈ (((Class.cv (nb078_alpha_dummy_940))).fv ∪ ((Class.cv (nb078_alpha_dummy_941))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0985 (h : Var) : (nb078_alpha_dummy_943 h) ∈ (((Class.cv (nb078_alpha_dummy_943 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_944 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0986 : (nb078_alpha_dummy_941) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_940)) (Class.cv (nb078_alpha_dummy_941)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_940)) (Class.cv (nb078_alpha_dummy_941)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0987 (h : Var) : (nb078_alpha_dummy_944 h) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_943 h)) (Class.cv (nb078_alpha_dummy_944 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_943 h)) (Class.cv (nb078_alpha_dummy_944 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0988 : (nb078_alpha_dummy_941) ∈ (((Class.cv (nb078_alpha_dummy_940))).fv ∪ ((Class.cv (nb078_alpha_dummy_941))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0989 (h : Var) : (nb078_alpha_dummy_944 h) ∈ (((Class.cv (nb078_alpha_dummy_943 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_944 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0990 : (nb078_alpha_dummy_940) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_940)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_941)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0991 (h : Var) : (nb078_alpha_dummy_943 h) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_943 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_944 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0992 : (nb078_alpha_dummy_940) ∈ (((Class.cv (nb078_alpha_dummy_940))).fv ∪ ((Class.cv (nb078_alpha_dummy_940))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0993 (h : Var) : (nb078_alpha_dummy_943 h) ∈ (((Class.cv (nb078_alpha_dummy_943 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_943 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0994 : (nb078_alpha_dummy_941) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_940)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_941)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0995 (h : Var) : (nb078_alpha_dummy_944 h) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_943 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_944 h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0996 : (nb078_alpha_dummy_941) ∈ (((Class.cv (nb078_alpha_dummy_941))).fv ∪ ((Class.cv (nb078_alpha_dummy_941))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0997 (h : Var) : (nb078_alpha_dummy_944 h) ∈ (((Class.cv (nb078_alpha_dummy_944 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_944 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0998 : (nb078_alpha_dummy_768) ∈ (((Class.cv (nb078_alpha_dummy_769))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0999 : (nb078_alpha_dummy_768) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_925) (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769)) (Wff.classEq (Class.cv (nb078_alpha_dummy_925)) (syn_cphi (Class.cv (nb078_alpha_dummy_926)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_925) (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_768)) (Wff.classEq (Class.cv (nb078_alpha_dummy_925)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_926))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0998) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0998) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1000 (h : Var) : (nb078_alpha_dummy_771 h) ∈ (((Class.cv (nb078_alpha_dummy_772 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1001 (h : Var) : (nb078_alpha_dummy_771 h) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_927 h) (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_927 h) (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_771 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1000 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1000 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1002 : (nb078_alpha_dummy_768) ∈ (((Class.cab (nb078_alpha_dummy_925) (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_768)) (Wff.classEq (Class.cv (nb078_alpha_dummy_925)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_926))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_925) (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_768)) (Wff.classEq (Class.cv (nb078_alpha_dummy_925)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_926))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0998) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0998) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1003 (h : Var) : (nb078_alpha_dummy_771 h) ∈ (((Class.cab (nb078_alpha_dummy_927 h) (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_771 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_927 h) (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_771 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1000 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1000 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1004 : (nb078_alpha_dummy_926) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_926))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1005 (h : Var) : (nb078_alpha_dummy_928 h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1006 : (nb078_alpha_dummy_926) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_926)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_926)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1007 (h : Var) : (nb078_alpha_dummy_928 h) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1008 : (nb078_alpha_dummy_962) ∈ (((Class.cv (nb078_alpha_dummy_962))).fv ∪ ((Class.cv (nb078_alpha_dummy_961))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1009 : (nb078_alpha_dummy_962) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_965) (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962)) (Wff.classEq (Class.cv (nb078_alpha_dummy_965)) (syn_cphi (Class.cv (nb078_alpha_dummy_966)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_965) (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961)) (Wff.classEq (Class.cv (nb078_alpha_dummy_965)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1008) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1008) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1010 (h : Var) : (nb078_alpha_dummy_964 h) ∈ (((Class.cv (nb078_alpha_dummy_964 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_963 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1011 (h : Var) : (nb078_alpha_dummy_964 h) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_967 h) (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_967 h) (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1010 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1010 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1012 : (nb078_alpha_dummy_962) ∈ (((Class.cab (nb078_alpha_dummy_965) (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962)) (Wff.classEq (Class.cv (nb078_alpha_dummy_965)) (syn_cphi (Class.cv (nb078_alpha_dummy_966))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_965) (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962)) (Wff.classEq (Class.cv (nb078_alpha_dummy_965)) (syn_cphi (Class.cv (nb078_alpha_dummy_966))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1008) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1008) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1013 (h : Var) : (nb078_alpha_dummy_964 h) ∈ (((Class.cab (nb078_alpha_dummy_967 h) (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_967 h) (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1010 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1010 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1014 : (nb078_alpha_dummy_966) ∈ (((Class.cv (nb078_alpha_dummy_966))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1015 (h : Var) : (nb078_alpha_dummy_968 h) ∈ (((Class.cv (nb078_alpha_dummy_968 h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1016 : (nb078_alpha_dummy_973) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_973)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_973)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_973))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
