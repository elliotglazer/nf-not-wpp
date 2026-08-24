import NAR4C090C001Part021

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

theorem nb090_support_mem_0885 (v : Var) : v ∈ (((syn_c1st)).fv ∪ ((Class.cv v)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0886 (v : Var) : v ∈ (({(nb090_alpha_dummy_828 v)} : Finset Var) ∪ ((syn_wbr (Class.cv v) (syn_c1st) (Class.cv (nb090_alpha_dummy_828 v)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0887 (v : Var) : v ∈ (((Class.cab (nb090_alpha_dummy_830 v) (Wff.classEq (Class.cab (nb090_alpha_dummy_828 v) (syn_wbr (Class.cv v) (syn_c1st) (Class.cv (nb090_alpha_dummy_828 v)))) (syn_csn (Class.cv (nb090_alpha_dummy_830 v)))))).fv) := by
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0886 v) 0))
  ·
    rw [fv_wff_classEq]
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0885 v) 0))
    ·
      rw [fv_syn_wbr]
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0888 (A : Class) : (nb090_alpha_dummy_002 A) ∈ (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_827 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0889 (A : Class) : (nb090_alpha_dummy_002 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_835 A) (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_835 A) (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_827 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0888 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0888 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0890 (v : Var) : v ∈ (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_828 v))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0891 (v : Var) : v ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v)) (syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv (nb090_alpha_dummy_828 v)) (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0890 v) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0890 v) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0892 (A : Class) : (nb090_alpha_dummy_002 A) ∈ (((Class.cab (nb090_alpha_dummy_835 A) (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_835 A) (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0888 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0888 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0893 (v : Var) : v ∈ (((Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v)) (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v)) (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0890 v) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0890 v) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0894 (A : Class) : (nb090_alpha_dummy_836 A) ∈ (((Class.cv (nb090_alpha_dummy_836 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0895 (v : Var) : (nb090_alpha_dummy_838 v) ∈ (((Class.cv (nb090_alpha_dummy_838 v))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0896 (A : Class) : (nb090_alpha_dummy_843 A) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_843 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_843 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_843 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0897 (v : Var) : (nb090_alpha_dummy_845 v) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_845 v)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_845 v)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_845 v))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0898 (A : Class) : (nb090_alpha_dummy_843 A) ∈ (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0899 (v : Var) : (nb090_alpha_dummy_845 v) ∈ (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0900 (A : Class) : (nb090_alpha_dummy_850 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_850 A)) (Class.cv (nb090_alpha_dummy_851 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_850 A)) (Class.cv (nb090_alpha_dummy_851 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0901 (v : Var) : (nb090_alpha_dummy_853 v) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_853 v)) (Class.cv (nb090_alpha_dummy_854 v)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_853 v)) (Class.cv (nb090_alpha_dummy_854 v)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0902 (A : Class) : (nb090_alpha_dummy_850 A) ∈ (((Class.cv (nb090_alpha_dummy_850 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_851 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0903 (v : Var) : (nb090_alpha_dummy_853 v) ∈ (((Class.cv (nb090_alpha_dummy_853 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_854 v))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0904 (A : Class) : (nb090_alpha_dummy_851 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_850 A)) (Class.cv (nb090_alpha_dummy_851 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_850 A)) (Class.cv (nb090_alpha_dummy_851 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0905 (v : Var) : (nb090_alpha_dummy_854 v) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_853 v)) (Class.cv (nb090_alpha_dummy_854 v)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_853 v)) (Class.cv (nb090_alpha_dummy_854 v)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0906 (A : Class) : (nb090_alpha_dummy_851 A) ∈ (((Class.cv (nb090_alpha_dummy_850 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_851 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0907 (v : Var) : (nb090_alpha_dummy_854 v) ∈ (((Class.cv (nb090_alpha_dummy_853 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_854 v))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0908 (A : Class) : (nb090_alpha_dummy_850 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_850 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_851 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0909 (v : Var) : (nb090_alpha_dummy_853 v) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_853 v)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_854 v)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0910 (A : Class) : (nb090_alpha_dummy_850 A) ∈ (((Class.cv (nb090_alpha_dummy_850 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_850 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0911 (v : Var) : (nb090_alpha_dummy_853 v) ∈ (((Class.cv (nb090_alpha_dummy_853 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_853 v))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0912 (A : Class) : (nb090_alpha_dummy_851 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_850 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_851 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0913 (v : Var) : (nb090_alpha_dummy_854 v) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_853 v)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_854 v)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0914 (A : Class) : (nb090_alpha_dummy_851 A) ∈ (((Class.cv (nb090_alpha_dummy_851 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_851 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0915 (v : Var) : (nb090_alpha_dummy_854 v) ∈ (((Class.cv (nb090_alpha_dummy_854 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_854 v))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0916 (A : Class) : (nb090_alpha_dummy_827 A) ∈ (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_827 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0917 (A : Class) : (nb090_alpha_dummy_827 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_835 A) (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_835 A) (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_827 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0916 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0916 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0918 (v : Var) : (nb090_alpha_dummy_828 v) ∈ (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_828 v))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0919 (v : Var) : (nb090_alpha_dummy_828 v) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v)) (syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv (nb090_alpha_dummy_828 v)) (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0918 v) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0918 v) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0920 (A : Class) : (nb090_alpha_dummy_827 A) ∈ (((Class.cab (nb090_alpha_dummy_835 A) (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_827 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_835 A) (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_827 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0916 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0916 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0921 (v : Var) : (nb090_alpha_dummy_828 v) ∈ (((Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv (nb090_alpha_dummy_828 v)) (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv (nb090_alpha_dummy_828 v)) (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0918 v) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0918 v) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0922 (A : Class) : (nb090_alpha_dummy_836 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0923 (v : Var) : (nb090_alpha_dummy_838 v) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0924 (A : Class) : (nb090_alpha_dummy_836 A) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0925 (v : Var) : (nb090_alpha_dummy_838 v) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0926 (A : Class) : (nb090_alpha_dummy_829 A) ∈ (((Class.cv (nb090_alpha_dummy_829 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0927 (v : Var) : (nb090_alpha_dummy_830 v) ∈ (((Class.cv (nb090_alpha_dummy_830 v))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_compact_fv_empty_0000 (A : Class) : (nb090_alpha_dummy_021 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0000 (A : Class) : (nb090_alpha_dummy_021 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_021, fv_syn_c1c] using (nb090_compact_fv_empty_0000 A)

theorem nb090_compact_fv_empty_0001 (v : Var) (u : Var) : (nb090_alpha_dummy_024 v u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0001 (v : Var) (u : Var) : (nb090_alpha_dummy_024 v u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_024, fv_syn_c1c] using (nb090_compact_fv_empty_0001 v u)

theorem nb090_compact_fv_empty_0002 (A : Class) : (nb090_alpha_dummy_020 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0002 (A : Class) : (nb090_alpha_dummy_020 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_020, fv_syn_c1c] using (nb090_compact_fv_empty_0002 A)

theorem nb090_compact_fv_empty_0003 (v : Var) (u : Var) : (nb090_alpha_dummy_023 v u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0003 (v : Var) (u : Var) : (nb090_alpha_dummy_023 v u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_023, fv_syn_c1c] using (nb090_compact_fv_empty_0003 v u)

theorem nb090_compact_fv_empty_0004 (A : Class) : (nb090_alpha_dummy_019 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0004 (A : Class) : (nb090_alpha_dummy_019 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_019, fv_syn_c1c] using (nb090_compact_fv_empty_0004 A)

theorem nb090_compact_fv_empty_0005 (v : Var) (u : Var) : (nb090_alpha_dummy_022 v u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0005 (v : Var) (u : Var) : (nb090_alpha_dummy_022 v u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_022, fv_syn_c1c] using (nb090_compact_fv_empty_0005 v u)

theorem nb090_compact_fv_empty_0006 (A : Class) : (nb090_alpha_dummy_017 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0006 (A : Class) : (nb090_alpha_dummy_017 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_017, fv_syn_c1c] using (nb090_compact_fv_empty_0006 A)

theorem nb090_compact_fv_empty_0007 (v : Var) (u : Var) : (nb090_alpha_dummy_018 v u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0007 (v : Var) (u : Var) : (nb090_alpha_dummy_018 v u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_018, fv_syn_c1c] using (nb090_compact_fv_empty_0007 v u)

theorem nb090_compact_fv_empty_0008 (A : Class) : (nb090_alpha_dummy_013 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0008 (A : Class) : (nb090_alpha_dummy_013 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_013, fv_syn_c1c] using (nb090_compact_fv_empty_0008 A)

theorem nb090_compact_fv_empty_0009 (v : Var) (u : Var) : (nb090_alpha_dummy_015 v u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0009 (v : Var) (u : Var) : (nb090_alpha_dummy_015 v u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_015, fv_syn_c1c] using (nb090_compact_fv_empty_0009 v u)

theorem nb090_compact_fv_empty_0010 (A : Class) : (nb090_alpha_dummy_014 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0010 (A : Class) : (nb090_alpha_dummy_014 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_014, fv_syn_c1c] using (nb090_compact_fv_empty_0010 A)

theorem nb090_compact_fv_empty_0011 (v : Var) (u : Var) : (nb090_alpha_dummy_016 v u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0011 (v : Var) (u : Var) : (nb090_alpha_dummy_016 v u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_016, fv_syn_c1c] using (nb090_compact_fv_empty_0011 v u)

theorem nb090_compact_fv_empty_0012 (A : Class) : (nb090_alpha_dummy_006 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0012 (A : Class) : (nb090_alpha_dummy_006 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_006, fv_syn_c1c] using (nb090_compact_fv_empty_0012 A)

theorem nb090_compact_fv_empty_0013 (v : Var) (u : Var) : (nb090_alpha_dummy_008 v u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0013 (v : Var) (u : Var) : (nb090_alpha_dummy_008 v u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_008, fv_syn_c1c] using (nb090_compact_fv_empty_0013 v u)

theorem nb090_compact_fv_empty_0014 (A : Class) : (nb090_alpha_dummy_005 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0014 (A : Class) : (nb090_alpha_dummy_005 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_005, fv_syn_c1c] using (nb090_compact_fv_empty_0014 A)

theorem nb090_compact_fv_empty_0015 (v : Var) (u : Var) : (nb090_alpha_dummy_007 v u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0015 (v : Var) (u : Var) : (nb090_alpha_dummy_007 v u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_007, fv_syn_c1c] using (nb090_compact_fv_empty_0015 v u)

theorem nb090_compact_fv_empty_0016 (A : Class) : (nb090_alpha_dummy_011 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0016 (A : Class) : (nb090_alpha_dummy_011 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_011, fv_syn_c1c] using (nb090_compact_fv_empty_0016 A)

theorem nb090_compact_fv_empty_0017 (v : Var) (u : Var) : (nb090_alpha_dummy_012 v u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0017 (v : Var) (u : Var) : (nb090_alpha_dummy_012 v u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_012, fv_syn_c1c] using (nb090_compact_fv_empty_0017 v u)

theorem nb090_compact_fv_empty_0018 (A : Class) : (nb090_alpha_dummy_009 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0018 (A : Class) : (nb090_alpha_dummy_009 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_009, fv_syn_c1c] using (nb090_compact_fv_empty_0018 A)

theorem nb090_compact_fv_empty_0019 (v : Var) (u : Var) : (nb090_alpha_dummy_010 v u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0019 (v : Var) (u : Var) : (nb090_alpha_dummy_010 v u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_010, fv_syn_c1c] using (nb090_compact_fv_empty_0019 v u)

theorem nb090_compact_fv_empty_0020 (A : Class) : (nb090_alpha_dummy_002 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0020 (A : Class) : (nb090_alpha_dummy_002 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_002, fv_syn_c1c] using (nb090_compact_fv_empty_0020 A)

theorem nb090_compact_fv_empty_0021 (v : Var) : v ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0021 (v : Var) : v ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb090_compact_fv_empty_0021 v)

theorem nb090_compact_fv_empty_0022 (A : Class) : (nb090_alpha_dummy_001 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0022 (A : Class) : (nb090_alpha_dummy_001 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_001, fv_syn_c1c] using (nb090_compact_fv_empty_0022 A)

theorem nb090_compact_fv_empty_0023 (u : Var) : u ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0023 (u : Var) : u ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb090_compact_fv_empty_0023 u)

theorem nb090_compact_fv_empty_0024 (A : Class) : (nb090_alpha_dummy_003 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0024 (A : Class) : (nb090_alpha_dummy_003 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_003, fv_syn_c1c] using (nb090_compact_fv_empty_0024 A)

theorem nb090_compact_fv_empty_0025 (v : Var) (u : Var) (A : Class) (h : Var) : (nb090_alpha_dummy_004 v u A h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0025 (v : Var) (u : Var) (A : Class) (h : Var) : (nb090_alpha_dummy_004 v u A h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_004, fv_syn_c1c] using (nb090_compact_fv_empty_0025 v u A h)

theorem nb090_compact_envfresh_0000 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_021 A), (nb090_alpha_dummy_024 v u)), ((nb090_alpha_dummy_020 A), (nb090_alpha_dummy_023 v u)), ((nb090_alpha_dummy_019 A), (nb090_alpha_dummy_022 v u)), ((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A), (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)), ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_011 A), (nb090_alpha_dummy_012 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_021 A) (nb090_alpha_dummy_024 v u) (nb090_wpp_notmem_0000 A) (nb090_wpp_notmem_0001 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_020 A) (nb090_alpha_dummy_023 v u) (nb090_wpp_notmem_0002 A) (nb090_wpp_notmem_0003 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_019 A) (nb090_alpha_dummy_022 v u) (nb090_wpp_notmem_0004 A) (nb090_wpp_notmem_0005 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_017 A) (nb090_alpha_dummy_018 v u) (nb090_wpp_notmem_0006 A) (nb090_wpp_notmem_0007 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_013 A) (nb090_alpha_dummy_015 v u) (nb090_wpp_notmem_0008 A) (nb090_wpp_notmem_0009 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_014 A) (nb090_alpha_dummy_016 v u) (nb090_wpp_notmem_0010 A) (nb090_wpp_notmem_0011 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_006 A) (nb090_alpha_dummy_008 v u) (nb090_wpp_notmem_0012 A) (nb090_wpp_notmem_0013 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_005 A) (nb090_alpha_dummy_007 v u) (nb090_wpp_notmem_0014 A) (nb090_wpp_notmem_0015 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_011 A) (nb090_alpha_dummy_012 v u) (nb090_wpp_notmem_0016 A) (nb090_wpp_notmem_0017 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_009 A) (nb090_alpha_dummy_010 v u) (nb090_wpp_notmem_0018 A) (nb090_wpp_notmem_0019 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0020 A) (nb090_wpp_notmem_0021 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0022 A) (nb090_wpp_notmem_0023 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0024 A) (nb090_wpp_notmem_0025 v u A h) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))

noncomputable def nb090_wpp_refl_0000 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_021 A), (nb090_alpha_dummy_024 v u)), ((nb090_alpha_dummy_020 A), (nb090_alpha_dummy_023 v u)), ((nb090_alpha_dummy_019 A), (nb090_alpha_dummy_022 v u)), ((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A), (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)), ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_011 A), (nb090_alpha_dummy_012 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0000 v u A h)

theorem nb090_wpp_notmem_0026 (A : Class) : (nb090_alpha_dummy_021 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_021, fv_syn_c0] using (nb090_compact_fv_empty_0000 A)

theorem nb090_wpp_notmem_0027 (v : Var) (u : Var) : (nb090_alpha_dummy_024 v u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_024, fv_syn_c0] using (nb090_compact_fv_empty_0001 v u)

theorem nb090_wpp_notmem_0028 (A : Class) : (nb090_alpha_dummy_020 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_020, fv_syn_c0] using (nb090_compact_fv_empty_0002 A)

theorem nb090_wpp_notmem_0029 (v : Var) (u : Var) : (nb090_alpha_dummy_023 v u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_023, fv_syn_c0] using (nb090_compact_fv_empty_0003 v u)

theorem nb090_wpp_notmem_0030 (A : Class) : (nb090_alpha_dummy_019 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_019, fv_syn_c0] using (nb090_compact_fv_empty_0004 A)

theorem nb090_wpp_notmem_0031 (v : Var) (u : Var) : (nb090_alpha_dummy_022 v u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_022, fv_syn_c0] using (nb090_compact_fv_empty_0005 v u)

theorem nb090_wpp_notmem_0032 (A : Class) : (nb090_alpha_dummy_017 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_017, fv_syn_c0] using (nb090_compact_fv_empty_0006 A)

theorem nb090_wpp_notmem_0033 (v : Var) (u : Var) : (nb090_alpha_dummy_018 v u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_018, fv_syn_c0] using (nb090_compact_fv_empty_0007 v u)

theorem nb090_wpp_notmem_0034 (A : Class) : (nb090_alpha_dummy_013 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_013, fv_syn_c0] using (nb090_compact_fv_empty_0008 A)

theorem nb090_wpp_notmem_0035 (v : Var) (u : Var) : (nb090_alpha_dummy_015 v u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_015, fv_syn_c0] using (nb090_compact_fv_empty_0009 v u)

theorem nb090_wpp_notmem_0036 (A : Class) : (nb090_alpha_dummy_014 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_014, fv_syn_c0] using (nb090_compact_fv_empty_0010 A)

theorem nb090_wpp_notmem_0037 (v : Var) (u : Var) : (nb090_alpha_dummy_016 v u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_016, fv_syn_c0] using (nb090_compact_fv_empty_0011 v u)

theorem nb090_wpp_notmem_0038 (A : Class) : (nb090_alpha_dummy_006 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_006, fv_syn_c0] using (nb090_compact_fv_empty_0012 A)

theorem nb090_wpp_notmem_0039 (v : Var) (u : Var) : (nb090_alpha_dummy_008 v u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_008, fv_syn_c0] using (nb090_compact_fv_empty_0013 v u)

theorem nb090_wpp_notmem_0040 (A : Class) : (nb090_alpha_dummy_005 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_005, fv_syn_c0] using (nb090_compact_fv_empty_0014 A)

theorem nb090_wpp_notmem_0041 (v : Var) (u : Var) : (nb090_alpha_dummy_007 v u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_007, fv_syn_c0] using (nb090_compact_fv_empty_0015 v u)

theorem nb090_wpp_notmem_0042 (A : Class) : (nb090_alpha_dummy_011 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_011, fv_syn_c0] using (nb090_compact_fv_empty_0016 A)

theorem nb090_wpp_notmem_0043 (v : Var) (u : Var) : (nb090_alpha_dummy_012 v u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_012, fv_syn_c0] using (nb090_compact_fv_empty_0017 v u)

theorem nb090_wpp_notmem_0044 (A : Class) : (nb090_alpha_dummy_009 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_009, fv_syn_c0] using (nb090_compact_fv_empty_0018 A)

theorem nb090_wpp_notmem_0045 (v : Var) (u : Var) : (nb090_alpha_dummy_010 v u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_010, fv_syn_c0] using (nb090_compact_fv_empty_0019 v u)

theorem nb090_wpp_notmem_0046 (A : Class) : (nb090_alpha_dummy_002 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_002, fv_syn_c0] using (nb090_compact_fv_empty_0020 A)

theorem nb090_wpp_notmem_0047 (v : Var) : v ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb090_compact_fv_empty_0021 v)

theorem nb090_wpp_notmem_0048 (A : Class) : (nb090_alpha_dummy_001 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_001, fv_syn_c0] using (nb090_compact_fv_empty_0022 A)

theorem nb090_wpp_notmem_0049 (u : Var) : u ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb090_compact_fv_empty_0023 u)

theorem nb090_wpp_notmem_0050 (A : Class) : (nb090_alpha_dummy_003 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_003, fv_syn_c0] using (nb090_compact_fv_empty_0024 A)

theorem nb090_wpp_notmem_0051 (v : Var) (u : Var) (A : Class) (h : Var) : (nb090_alpha_dummy_004 v u A h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_004, fv_syn_c0] using (nb090_compact_fv_empty_0025 v u A h)

theorem nb090_compact_envfresh_0001 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_021 A), (nb090_alpha_dummy_024 v u)), ((nb090_alpha_dummy_020 A), (nb090_alpha_dummy_023 v u)), ((nb090_alpha_dummy_019 A), (nb090_alpha_dummy_022 v u)), ((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A), (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)), ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_011 A), (nb090_alpha_dummy_012 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_021 A) (nb090_alpha_dummy_024 v u) (nb090_wpp_notmem_0026 A) (nb090_wpp_notmem_0027 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_020 A) (nb090_alpha_dummy_023 v u) (nb090_wpp_notmem_0028 A) (nb090_wpp_notmem_0029 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_019 A) (nb090_alpha_dummy_022 v u) (nb090_wpp_notmem_0030 A) (nb090_wpp_notmem_0031 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_017 A) (nb090_alpha_dummy_018 v u) (nb090_wpp_notmem_0032 A) (nb090_wpp_notmem_0033 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_013 A) (nb090_alpha_dummy_015 v u) (nb090_wpp_notmem_0034 A) (nb090_wpp_notmem_0035 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_014 A) (nb090_alpha_dummy_016 v u) (nb090_wpp_notmem_0036 A) (nb090_wpp_notmem_0037 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_006 A) (nb090_alpha_dummy_008 v u) (nb090_wpp_notmem_0038 A) (nb090_wpp_notmem_0039 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_005 A) (nb090_alpha_dummy_007 v u) (nb090_wpp_notmem_0040 A) (nb090_wpp_notmem_0041 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_011 A) (nb090_alpha_dummy_012 v u) (nb090_wpp_notmem_0042 A) (nb090_wpp_notmem_0043 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_009 A) (nb090_alpha_dummy_010 v u) (nb090_wpp_notmem_0044 A) (nb090_wpp_notmem_0045 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0046 A) (nb090_wpp_notmem_0047 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0048 A) (nb090_wpp_notmem_0049 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0050 A) (nb090_wpp_notmem_0051 v u A h) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))

noncomputable def nb090_wpp_refl_0001 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_021 A), (nb090_alpha_dummy_024 v u)), ((nb090_alpha_dummy_020 A), (nb090_alpha_dummy_023 v u)), ((nb090_alpha_dummy_019 A), (nb090_alpha_dummy_022 v u)), ((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A), (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)), ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_011 A), (nb090_alpha_dummy_012 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0001 v u A h)

theorem nb090_wpp_notmem_0052 (A : Class) : (nb090_alpha_dummy_017 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_017, fv_syn_cnnc] using (nb090_compact_fv_empty_0006 A)

theorem nb090_wpp_notmem_0053 (v : Var) (u : Var) : (nb090_alpha_dummy_018 v u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_018, fv_syn_cnnc] using (nb090_compact_fv_empty_0007 v u)

theorem nb090_wpp_notmem_0054 (A : Class) : (nb090_alpha_dummy_013 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_013, fv_syn_cnnc] using (nb090_compact_fv_empty_0008 A)

theorem nb090_wpp_notmem_0055 (v : Var) (u : Var) : (nb090_alpha_dummy_015 v u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_015, fv_syn_cnnc] using (nb090_compact_fv_empty_0009 v u)

theorem nb090_wpp_notmem_0056 (A : Class) : (nb090_alpha_dummy_014 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_014, fv_syn_cnnc] using (nb090_compact_fv_empty_0010 A)

theorem nb090_wpp_notmem_0057 (v : Var) (u : Var) : (nb090_alpha_dummy_016 v u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_016, fv_syn_cnnc] using (nb090_compact_fv_empty_0011 v u)

theorem nb090_wpp_notmem_0058 (A : Class) : (nb090_alpha_dummy_006 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_006, fv_syn_cnnc] using (nb090_compact_fv_empty_0012 A)

theorem nb090_wpp_notmem_0059 (v : Var) (u : Var) : (nb090_alpha_dummy_008 v u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_008, fv_syn_cnnc] using (nb090_compact_fv_empty_0013 v u)

theorem nb090_wpp_notmem_0060 (A : Class) : (nb090_alpha_dummy_005 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_005, fv_syn_cnnc] using (nb090_compact_fv_empty_0014 A)

theorem nb090_wpp_notmem_0061 (v : Var) (u : Var) : (nb090_alpha_dummy_007 v u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_007, fv_syn_cnnc] using (nb090_compact_fv_empty_0015 v u)

theorem nb090_wpp_notmem_0062 (A : Class) : (nb090_alpha_dummy_011 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_011, fv_syn_cnnc] using (nb090_compact_fv_empty_0016 A)

theorem nb090_wpp_notmem_0063 (v : Var) (u : Var) : (nb090_alpha_dummy_012 v u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_012, fv_syn_cnnc] using (nb090_compact_fv_empty_0017 v u)

theorem nb090_wpp_notmem_0064 (A : Class) : (nb090_alpha_dummy_009 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_009, fv_syn_cnnc] using (nb090_compact_fv_empty_0018 A)

theorem nb090_wpp_notmem_0065 (v : Var) (u : Var) : (nb090_alpha_dummy_010 v u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_010, fv_syn_cnnc] using (nb090_compact_fv_empty_0019 v u)

theorem nb090_wpp_notmem_0066 (A : Class) : (nb090_alpha_dummy_002 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_002, fv_syn_cnnc] using (nb090_compact_fv_empty_0020 A)

theorem nb090_wpp_notmem_0067 (v : Var) : v ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb090_compact_fv_empty_0021 v)

theorem nb090_wpp_notmem_0068 (A : Class) : (nb090_alpha_dummy_001 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_001, fv_syn_cnnc] using (nb090_compact_fv_empty_0022 A)

theorem nb090_wpp_notmem_0069 (u : Var) : u ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb090_compact_fv_empty_0023 u)

theorem nb090_wpp_notmem_0070 (A : Class) : (nb090_alpha_dummy_003 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_003, fv_syn_cnnc] using (nb090_compact_fv_empty_0024 A)

theorem nb090_wpp_notmem_0071 (v : Var) (u : Var) (A : Class) (h : Var) : (nb090_alpha_dummy_004 v u A h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_004, fv_syn_cnnc] using (nb090_compact_fv_empty_0025 v u A h)

theorem nb090_compact_envfresh_0002 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A), (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)), ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_011 A), (nb090_alpha_dummy_012 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_017 A) (nb090_alpha_dummy_018 v u) (nb090_wpp_notmem_0052 A) (nb090_wpp_notmem_0053 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_013 A) (nb090_alpha_dummy_015 v u) (nb090_wpp_notmem_0054 A) (nb090_wpp_notmem_0055 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_014 A) (nb090_alpha_dummy_016 v u) (nb090_wpp_notmem_0056 A) (nb090_wpp_notmem_0057 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_006 A) (nb090_alpha_dummy_008 v u) (nb090_wpp_notmem_0058 A) (nb090_wpp_notmem_0059 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_005 A) (nb090_alpha_dummy_007 v u) (nb090_wpp_notmem_0060 A) (nb090_wpp_notmem_0061 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_011 A) (nb090_alpha_dummy_012 v u) (nb090_wpp_notmem_0062 A) (nb090_wpp_notmem_0063 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_009 A) (nb090_alpha_dummy_010 v u) (nb090_wpp_notmem_0064 A) (nb090_wpp_notmem_0065 v u) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0066 A) (nb090_wpp_notmem_0067 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0068 A) (nb090_wpp_notmem_0069 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0070 A) (nb090_wpp_notmem_0071 v u A h) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))

noncomputable def nb090_wpp_refl_0002 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A), (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)), ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_011 A), (nb090_alpha_dummy_012 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0002 v u A h)

theorem nb090_compact_fv_empty_0026 (A : Class) : (nb090_alpha_dummy_039 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0072 (A : Class) : (nb090_alpha_dummy_039 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_039, fv_syn_c1c] using (nb090_compact_fv_empty_0026 A)

theorem nb090_compact_fv_empty_0027 (v : Var) (u : Var) : (nb090_alpha_dummy_040 v u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
