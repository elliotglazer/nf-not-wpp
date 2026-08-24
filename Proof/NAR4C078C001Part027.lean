import NAR4C078C001Part026

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

theorem nb078_support_mem_0741 (g : Var) : (nb078_alpha_dummy_651 g) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_693 g) (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_652 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_693 g) (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_651 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0740 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0740 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0742 : (nb078_alpha_dummy_649) ∈ (((Class.cab (nb078_alpha_dummy_691) (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_649)) (Wff.classEq (Class.cv (nb078_alpha_dummy_691)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_692))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_691) (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_649)) (Wff.classEq (Class.cv (nb078_alpha_dummy_691)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_692))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0738) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0738) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0743 (g : Var) : (nb078_alpha_dummy_651 g) ∈ (((Class.cab (nb078_alpha_dummy_693 g) (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_651 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_693 g) (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_651 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0740 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0740 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0744 : (nb078_alpha_dummy_692) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_692))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0745 (g : Var) : (nb078_alpha_dummy_694 g) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0746 : (nb078_alpha_dummy_692) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_692)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_692)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0747 (g : Var) : (nb078_alpha_dummy_694 g) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0748 : (nb078_alpha_dummy_001) ∈ (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))) (syn_cid))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0749 (g : Var) : g ∈ (((syn_cnin (syn_ccom (syn_ccnv (Class.cv g)) (syn_ccnv (syn_ccnv (Class.cv g)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv g)) (syn_ccnv (syn_ccnv (Class.cv g)))) (syn_cid))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0750 : (nb078_alpha_dummy_001) ∈ (((syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))))).fv ∪ ((syn_cid)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0751 (g : Var) : g ∈ (((syn_ccom (syn_ccnv (Class.cv g)) (syn_ccnv (syn_ccnv (Class.cv g))))).fv ∪ ((syn_cid)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0752 : (nb078_alpha_dummy_001) ∈ (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0753 : (nb078_alpha_dummy_001) ∈ (({(nb078_alpha_dummy_569)} : Finset Var) ∪ ({(nb078_alpha_dummy_570)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_571) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_569)) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))) (Class.cv (nb078_alpha_dummy_571))) (syn_wbr (Class.cv (nb078_alpha_dummy_571)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_570)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0752) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_left
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_syn_ccnv]
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb078_support_mem_0754 (g : Var) : g ∈ (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0755 (g : Var) : g ∈ (({(nb078_alpha_dummy_572 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_573 g)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_574 g) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_572 g)) (syn_ccnv (syn_ccnv (Class.cv g))) (Class.cv (nb078_alpha_dummy_574 g))) (syn_wbr (Class.cv (nb078_alpha_dummy_574 g)) (syn_ccnv (Class.cv g)) (Class.cv (nb078_alpha_dummy_573 g)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0754 g) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_left
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_syn_ccnv]
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb078_support_mem_0756 : (nb078_alpha_dummy_001) ∈ (({(nb078_alpha_dummy_649)} : Finset Var) ∪ ({(nb078_alpha_dummy_650)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_650)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_649)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0757 (g : Var) : g ∈ (({(nb078_alpha_dummy_651 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_652 g)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_652 g)) (syn_ccnv (Class.cv g)) (Class.cv (nb078_alpha_dummy_651 g)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0758 : (nb078_alpha_dummy_001) ∈ (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) := by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0759 (g : Var) : g ∈ (((syn_ccnv (Class.cv g))).fv) := by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0760 : (nb078_alpha_dummy_571) ∈ (((Class.cv (nb078_alpha_dummy_571))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0761 : (nb078_alpha_dummy_571) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_727) (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_571)) (Wff.classEq (Class.cv (nb078_alpha_dummy_727)) (syn_cphi (Class.cv (nb078_alpha_dummy_728)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_727) (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_570)) (Wff.classEq (Class.cv (nb078_alpha_dummy_727)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_728))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0760) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0760) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0762 (g : Var) : (nb078_alpha_dummy_574 g) ∈ (((Class.cv (nb078_alpha_dummy_574 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0763 (g : Var) : (nb078_alpha_dummy_574 g) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_729 g) (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_574 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_729 g) (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_573 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0762 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0762 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0764 : (nb078_alpha_dummy_571) ∈ (((Class.cab (nb078_alpha_dummy_727) (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_571)) (Wff.classEq (Class.cv (nb078_alpha_dummy_727)) (syn_cphi (Class.cv (nb078_alpha_dummy_728))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_727) (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_571)) (Wff.classEq (Class.cv (nb078_alpha_dummy_727)) (syn_cphi (Class.cv (nb078_alpha_dummy_728))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0760) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0760) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0765 (g : Var) : (nb078_alpha_dummy_574 g) ∈ (((Class.cab (nb078_alpha_dummy_729 g) (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_574 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_729 g) (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_574 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0762 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0762 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0766 : (nb078_alpha_dummy_728) ∈ (((Class.cv (nb078_alpha_dummy_728))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0767 (g : Var) : (nb078_alpha_dummy_730 g) ∈ (((Class.cv (nb078_alpha_dummy_730 g))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0768 : (nb078_alpha_dummy_735) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_735)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_735)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_735))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0769 (g : Var) : (nb078_alpha_dummy_737 g) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_737 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_737 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_737 g))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0770 : (nb078_alpha_dummy_735) ∈ (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0771 (g : Var) : (nb078_alpha_dummy_737 g) ∈ (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0772 : (nb078_alpha_dummy_742) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_742)) (Class.cv (nb078_alpha_dummy_743)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_742)) (Class.cv (nb078_alpha_dummy_743)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0773 (g : Var) : (nb078_alpha_dummy_745 g) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_745 g)) (Class.cv (nb078_alpha_dummy_746 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_745 g)) (Class.cv (nb078_alpha_dummy_746 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0774 : (nb078_alpha_dummy_742) ∈ (((Class.cv (nb078_alpha_dummy_742))).fv ∪ ((Class.cv (nb078_alpha_dummy_743))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0775 (g : Var) : (nb078_alpha_dummy_745 g) ∈ (((Class.cv (nb078_alpha_dummy_745 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_746 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0776 : (nb078_alpha_dummy_743) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_742)) (Class.cv (nb078_alpha_dummy_743)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_742)) (Class.cv (nb078_alpha_dummy_743)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0777 (g : Var) : (nb078_alpha_dummy_746 g) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_745 g)) (Class.cv (nb078_alpha_dummy_746 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_745 g)) (Class.cv (nb078_alpha_dummy_746 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0778 : (nb078_alpha_dummy_743) ∈ (((Class.cv (nb078_alpha_dummy_742))).fv ∪ ((Class.cv (nb078_alpha_dummy_743))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0779 (g : Var) : (nb078_alpha_dummy_746 g) ∈ (((Class.cv (nb078_alpha_dummy_745 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_746 g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0780 : (nb078_alpha_dummy_742) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_742)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_743)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0781 (g : Var) : (nb078_alpha_dummy_745 g) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_745 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_746 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0782 : (nb078_alpha_dummy_742) ∈ (((Class.cv (nb078_alpha_dummy_742))).fv ∪ ((Class.cv (nb078_alpha_dummy_742))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0783 (g : Var) : (nb078_alpha_dummy_745 g) ∈ (((Class.cv (nb078_alpha_dummy_745 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_745 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0784 : (nb078_alpha_dummy_743) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_742)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_743)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0785 (g : Var) : (nb078_alpha_dummy_746 g) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_745 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_746 g)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0786 : (nb078_alpha_dummy_743) ∈ (((Class.cv (nb078_alpha_dummy_743))).fv ∪ ((Class.cv (nb078_alpha_dummy_743))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0787 (g : Var) : (nb078_alpha_dummy_746 g) ∈ (((Class.cv (nb078_alpha_dummy_746 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_746 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0788 : (nb078_alpha_dummy_570) ∈ (((Class.cv (nb078_alpha_dummy_571))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0789 : (nb078_alpha_dummy_570) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_727) (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_571)) (Wff.classEq (Class.cv (nb078_alpha_dummy_727)) (syn_cphi (Class.cv (nb078_alpha_dummy_728)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_727) (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_570)) (Wff.classEq (Class.cv (nb078_alpha_dummy_727)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_728))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0788) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0788) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0790 (g : Var) : (nb078_alpha_dummy_573 g) ∈ (((Class.cv (nb078_alpha_dummy_574 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0791 (g : Var) : (nb078_alpha_dummy_573 g) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_729 g) (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_574 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_729 g) (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_573 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0790 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0790 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0792 : (nb078_alpha_dummy_570) ∈ (((Class.cab (nb078_alpha_dummy_727) (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_570)) (Wff.classEq (Class.cv (nb078_alpha_dummy_727)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_728))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_727) (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_570)) (Wff.classEq (Class.cv (nb078_alpha_dummy_727)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_728))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0788) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0788) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0793 (g : Var) : (nb078_alpha_dummy_573 g) ∈ (((Class.cab (nb078_alpha_dummy_729 g) (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_573 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_729 g) (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_573 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0790 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0790 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0794 : (nb078_alpha_dummy_728) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_728))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0795 (g : Var) : (nb078_alpha_dummy_730 g) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0796 : (nb078_alpha_dummy_728) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_728)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_728)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0797 (g : Var) : (nb078_alpha_dummy_730 g) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0798 : (nb078_alpha_dummy_767) ∈ (({(nb078_alpha_dummy_767)} : Finset Var) ∪ ({(nb078_alpha_dummy_768)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_769) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_767)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_769))) (syn_wbr (Class.cv (nb078_alpha_dummy_769)) (Class.cv (nb078_alpha_dummy_002)) (Class.cv (nb078_alpha_dummy_768)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0799 (h : Var) : (nb078_alpha_dummy_770 h) ∈ (({(nb078_alpha_dummy_770 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_771 h)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_772 h) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_770 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb078_alpha_dummy_772 h))) (syn_wbr (Class.cv (nb078_alpha_dummy_772 h)) (Class.cv h) (Class.cv (nb078_alpha_dummy_771 h)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0800 : (nb078_alpha_dummy_768) ∈ (({(nb078_alpha_dummy_767)} : Finset Var) ∪ ({(nb078_alpha_dummy_768)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_769) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_767)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_769))) (syn_wbr (Class.cv (nb078_alpha_dummy_769)) (Class.cv (nb078_alpha_dummy_002)) (Class.cv (nb078_alpha_dummy_768)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0801 (h : Var) : (nb078_alpha_dummy_771 h) ∈ (({(nb078_alpha_dummy_770 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_771 h)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_772 h) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_770 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb078_alpha_dummy_772 h))) (syn_wbr (Class.cv (nb078_alpha_dummy_772 h)) (Class.cv h) (Class.cv (nb078_alpha_dummy_771 h)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0802 : (nb078_alpha_dummy_767) ∈ (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0803 : (nb078_alpha_dummy_767) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_775) (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_767)) (Wff.classEq (Class.cv (nb078_alpha_dummy_775)) (syn_cphi (Class.cv (nb078_alpha_dummy_776)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_775) (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_768)) (Wff.classEq (Class.cv (nb078_alpha_dummy_775)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_776))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0802) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0802) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0804 (h : Var) : (nb078_alpha_dummy_770 h) ∈ (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0805 (h : Var) : (nb078_alpha_dummy_770 h) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_777 h) (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_770 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_777 h) (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_771 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0804 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0804 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0806 : (nb078_alpha_dummy_767) ∈ (((Class.cab (nb078_alpha_dummy_775) (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_767)) (Wff.classEq (Class.cv (nb078_alpha_dummy_775)) (syn_cphi (Class.cv (nb078_alpha_dummy_776))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_775) (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_767)) (Wff.classEq (Class.cv (nb078_alpha_dummy_775)) (syn_cphi (Class.cv (nb078_alpha_dummy_776))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0802) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0802) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0807 (h : Var) : (nb078_alpha_dummy_770 h) ∈ (((Class.cab (nb078_alpha_dummy_777 h) (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_770 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_777 h) (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_770 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0804 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0804 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0808 : (nb078_alpha_dummy_776) ∈ (((Class.cv (nb078_alpha_dummy_776))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0809 (h : Var) : (nb078_alpha_dummy_778 h) ∈ (((Class.cv (nb078_alpha_dummy_778 h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0810 : (nb078_alpha_dummy_783) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_783)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_783)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_783))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0811 (h : Var) : (nb078_alpha_dummy_785 h) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_785 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_785 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_785 h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0812 : (nb078_alpha_dummy_783) ∈ (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0813 (h : Var) : (nb078_alpha_dummy_785 h) ∈ (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0814 : (nb078_alpha_dummy_790) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_790)) (Class.cv (nb078_alpha_dummy_791)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_790)) (Class.cv (nb078_alpha_dummy_791)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0815 (h : Var) : (nb078_alpha_dummy_793 h) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_793 h)) (Class.cv (nb078_alpha_dummy_794 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_793 h)) (Class.cv (nb078_alpha_dummy_794 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0816 : (nb078_alpha_dummy_790) ∈ (((Class.cv (nb078_alpha_dummy_790))).fv ∪ ((Class.cv (nb078_alpha_dummy_791))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0817 (h : Var) : (nb078_alpha_dummy_793 h) ∈ (((Class.cv (nb078_alpha_dummy_793 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_794 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0818 : (nb078_alpha_dummy_791) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_790)) (Class.cv (nb078_alpha_dummy_791)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_790)) (Class.cv (nb078_alpha_dummy_791)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0819 (h : Var) : (nb078_alpha_dummy_794 h) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_793 h)) (Class.cv (nb078_alpha_dummy_794 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_793 h)) (Class.cv (nb078_alpha_dummy_794 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0820 : (nb078_alpha_dummy_791) ∈ (((Class.cv (nb078_alpha_dummy_790))).fv ∪ ((Class.cv (nb078_alpha_dummy_791))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0821 (h : Var) : (nb078_alpha_dummy_794 h) ∈ (((Class.cv (nb078_alpha_dummy_793 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_794 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0822 : (nb078_alpha_dummy_790) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_790)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_791)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0823 (h : Var) : (nb078_alpha_dummy_793 h) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_793 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_794 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0824 : (nb078_alpha_dummy_790) ∈ (((Class.cv (nb078_alpha_dummy_790))).fv ∪ ((Class.cv (nb078_alpha_dummy_790))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0825 (h : Var) : (nb078_alpha_dummy_793 h) ∈ (((Class.cv (nb078_alpha_dummy_793 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_793 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0826 : (nb078_alpha_dummy_791) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_790)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_791)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0827 (h : Var) : (nb078_alpha_dummy_794 h) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_793 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_794 h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0828 : (nb078_alpha_dummy_791) ∈ (((Class.cv (nb078_alpha_dummy_791))).fv ∪ ((Class.cv (nb078_alpha_dummy_791))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0829 (h : Var) : (nb078_alpha_dummy_794 h) ∈ (((Class.cv (nb078_alpha_dummy_794 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_794 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0830 : (nb078_alpha_dummy_768) ∈ (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0831 : (nb078_alpha_dummy_768) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_775) (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_767)) (Wff.classEq (Class.cv (nb078_alpha_dummy_775)) (syn_cphi (Class.cv (nb078_alpha_dummy_776)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_775) (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_768)) (Wff.classEq (Class.cv (nb078_alpha_dummy_775)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_776))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0830) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0830) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0832 (h : Var) : (nb078_alpha_dummy_771 h) ∈ (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0833 (h : Var) : (nb078_alpha_dummy_771 h) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_777 h) (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_770 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_777 h) (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_771 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0832 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0832 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0834 : (nb078_alpha_dummy_768) ∈ (((Class.cab (nb078_alpha_dummy_775) (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_768)) (Wff.classEq (Class.cv (nb078_alpha_dummy_775)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_776))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_775) (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_768)) (Wff.classEq (Class.cv (nb078_alpha_dummy_775)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_776))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0830) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0830) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0835 (h : Var) : (nb078_alpha_dummy_771 h) ∈ (((Class.cab (nb078_alpha_dummy_777 h) (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_771 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_777 h) (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_771 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0832 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0832 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0836 : (nb078_alpha_dummy_776) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_776))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0837 (h : Var) : (nb078_alpha_dummy_778 h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0838 : (nb078_alpha_dummy_776) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_776)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_776)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0839 (h : Var) : (nb078_alpha_dummy_778 h) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0840 : (nb078_alpha_dummy_767) ∈ (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_769))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0841 : (nb078_alpha_dummy_767) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_811) (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767)) (Wff.classEq (Class.cv (nb078_alpha_dummy_811)) (syn_cphi (Class.cv (nb078_alpha_dummy_812)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_811) (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_769)) (Wff.classEq (Class.cv (nb078_alpha_dummy_811)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_812))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0840) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0840) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0842 (h : Var) : (nb078_alpha_dummy_770 h) ∈ (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_772 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0843 (h : Var) : (nb078_alpha_dummy_770 h) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_813 h) (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_813 h) (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_772 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0842 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0842 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0844 : (nb078_alpha_dummy_767) ∈ (((Class.cab (nb078_alpha_dummy_811) (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767)) (Wff.classEq (Class.cv (nb078_alpha_dummy_811)) (syn_cphi (Class.cv (nb078_alpha_dummy_812))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_811) (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767)) (Wff.classEq (Class.cv (nb078_alpha_dummy_811)) (syn_cphi (Class.cv (nb078_alpha_dummy_812))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0840) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0840) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0845 (h : Var) : (nb078_alpha_dummy_770 h) ∈ (((Class.cab (nb078_alpha_dummy_813 h) (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_813 h) (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0842 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0842 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0846 : (nb078_alpha_dummy_812) ∈ (((Class.cv (nb078_alpha_dummy_812))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0847 (h : Var) : (nb078_alpha_dummy_814 h) ∈ (((Class.cv (nb078_alpha_dummy_814 h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0848 : (nb078_alpha_dummy_819) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_819)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_819)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_819))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0849 (h : Var) : (nb078_alpha_dummy_821 h) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_821 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_821 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_821 h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0850 : (nb078_alpha_dummy_819) ∈ (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0851 (h : Var) : (nb078_alpha_dummy_821 h) ∈ (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0852 : (nb078_alpha_dummy_826) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_826)) (Class.cv (nb078_alpha_dummy_827)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_826)) (Class.cv (nb078_alpha_dummy_827)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0853 (h : Var) : (nb078_alpha_dummy_829 h) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_829 h)) (Class.cv (nb078_alpha_dummy_830 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_829 h)) (Class.cv (nb078_alpha_dummy_830 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0854 : (nb078_alpha_dummy_826) ∈ (((Class.cv (nb078_alpha_dummy_826))).fv ∪ ((Class.cv (nb078_alpha_dummy_827))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0855 (h : Var) : (nb078_alpha_dummy_829 h) ∈ (((Class.cv (nb078_alpha_dummy_829 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_830 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0856 : (nb078_alpha_dummy_827) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_826)) (Class.cv (nb078_alpha_dummy_827)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_826)) (Class.cv (nb078_alpha_dummy_827)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0857 (h : Var) : (nb078_alpha_dummy_830 h) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_829 h)) (Class.cv (nb078_alpha_dummy_830 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_829 h)) (Class.cv (nb078_alpha_dummy_830 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0858 : (nb078_alpha_dummy_827) ∈ (((Class.cv (nb078_alpha_dummy_826))).fv ∪ ((Class.cv (nb078_alpha_dummy_827))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0859 (h : Var) : (nb078_alpha_dummy_830 h) ∈ (((Class.cv (nb078_alpha_dummy_829 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_830 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0860 : (nb078_alpha_dummy_826) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_826)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_827)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0861 (h : Var) : (nb078_alpha_dummy_829 h) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_829 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_830 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0862 : (nb078_alpha_dummy_826) ∈ (((Class.cv (nb078_alpha_dummy_826))).fv ∪ ((Class.cv (nb078_alpha_dummy_826))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0863 (h : Var) : (nb078_alpha_dummy_829 h) ∈ (((Class.cv (nb078_alpha_dummy_829 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_829 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0864 : (nb078_alpha_dummy_827) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_826)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_827)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0865 (h : Var) : (nb078_alpha_dummy_830 h) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_829 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_830 h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0866 : (nb078_alpha_dummy_827) ∈ (((Class.cv (nb078_alpha_dummy_827))).fv ∪ ((Class.cv (nb078_alpha_dummy_827))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0867 (h : Var) : (nb078_alpha_dummy_830 h) ∈ (((Class.cv (nb078_alpha_dummy_830 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_830 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0868 : (nb078_alpha_dummy_769) ∈ (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_769))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0869 : (nb078_alpha_dummy_769) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_811) (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767)) (Wff.classEq (Class.cv (nb078_alpha_dummy_811)) (syn_cphi (Class.cv (nb078_alpha_dummy_812)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_811) (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_769)) (Wff.classEq (Class.cv (nb078_alpha_dummy_811)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_812))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0868) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0868) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0870 (h : Var) : (nb078_alpha_dummy_772 h) ∈ (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_772 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0871 (h : Var) : (nb078_alpha_dummy_772 h) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_813 h) (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_813 h) (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_772 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0870 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0870 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0872 : (nb078_alpha_dummy_769) ∈ (((Class.cab (nb078_alpha_dummy_811) (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_769)) (Wff.classEq (Class.cv (nb078_alpha_dummy_811)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_812))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_811) (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_769)) (Wff.classEq (Class.cv (nb078_alpha_dummy_811)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_812))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0868) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0868) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0873 (h : Var) : (nb078_alpha_dummy_772 h) ∈ (((Class.cab (nb078_alpha_dummy_813 h) (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_772 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_813 h) (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_772 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0870 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0870 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0874 : (nb078_alpha_dummy_812) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_812))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0875 (h : Var) : (nb078_alpha_dummy_814 h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0876 : (nb078_alpha_dummy_812) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_812)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_812)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0877 (h : Var) : (nb078_alpha_dummy_814 h) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
