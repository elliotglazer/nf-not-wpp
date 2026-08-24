import NAR4C078C001Part025

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

theorem nb078_support_mem_0596 : (nb078_alpha_dummy_569) ∈ (((Class.cab (nb078_alpha_dummy_577) (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_569)) (Wff.classEq (Class.cv (nb078_alpha_dummy_577)) (syn_cphi (Class.cv (nb078_alpha_dummy_578))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_577) (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_569)) (Wff.classEq (Class.cv (nb078_alpha_dummy_577)) (syn_cphi (Class.cv (nb078_alpha_dummy_578))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0592) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0592) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0597 (g : Var) : (nb078_alpha_dummy_572 g) ∈ (((Class.cab (nb078_alpha_dummy_579 g) (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_572 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_579 g) (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_572 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0594 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0594 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0598 : (nb078_alpha_dummy_578) ∈ (((Class.cv (nb078_alpha_dummy_578))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0599 (g : Var) : (nb078_alpha_dummy_580 g) ∈ (((Class.cv (nb078_alpha_dummy_580 g))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0600 : (nb078_alpha_dummy_585) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_585)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_585)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_585))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0601 (g : Var) : (nb078_alpha_dummy_587 g) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_587 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_587 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_587 g))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0602 : (nb078_alpha_dummy_585) ∈ (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0603 (g : Var) : (nb078_alpha_dummy_587 g) ∈ (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0604 : (nb078_alpha_dummy_592) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_592)) (Class.cv (nb078_alpha_dummy_593)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_592)) (Class.cv (nb078_alpha_dummy_593)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0605 (g : Var) : (nb078_alpha_dummy_595 g) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_595 g)) (Class.cv (nb078_alpha_dummy_596 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_595 g)) (Class.cv (nb078_alpha_dummy_596 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0606 : (nb078_alpha_dummy_592) ∈ (((Class.cv (nb078_alpha_dummy_592))).fv ∪ ((Class.cv (nb078_alpha_dummy_593))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0607 (g : Var) : (nb078_alpha_dummy_595 g) ∈ (((Class.cv (nb078_alpha_dummy_595 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_596 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0608 : (nb078_alpha_dummy_593) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_592)) (Class.cv (nb078_alpha_dummy_593)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_592)) (Class.cv (nb078_alpha_dummy_593)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0609 (g : Var) : (nb078_alpha_dummy_596 g) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_595 g)) (Class.cv (nb078_alpha_dummy_596 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_595 g)) (Class.cv (nb078_alpha_dummy_596 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0610 : (nb078_alpha_dummy_593) ∈ (((Class.cv (nb078_alpha_dummy_592))).fv ∪ ((Class.cv (nb078_alpha_dummy_593))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0611 (g : Var) : (nb078_alpha_dummy_596 g) ∈ (((Class.cv (nb078_alpha_dummy_595 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_596 g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0612 : (nb078_alpha_dummy_592) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_592)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_593)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0613 (g : Var) : (nb078_alpha_dummy_595 g) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_595 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_596 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0614 : (nb078_alpha_dummy_592) ∈ (((Class.cv (nb078_alpha_dummy_592))).fv ∪ ((Class.cv (nb078_alpha_dummy_592))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0615 (g : Var) : (nb078_alpha_dummy_595 g) ∈ (((Class.cv (nb078_alpha_dummy_595 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_595 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0616 : (nb078_alpha_dummy_593) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_592)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_593)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0617 (g : Var) : (nb078_alpha_dummy_596 g) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_595 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_596 g)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0618 : (nb078_alpha_dummy_593) ∈ (((Class.cv (nb078_alpha_dummy_593))).fv ∪ ((Class.cv (nb078_alpha_dummy_593))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0619 (g : Var) : (nb078_alpha_dummy_596 g) ∈ (((Class.cv (nb078_alpha_dummy_596 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_596 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0620 : (nb078_alpha_dummy_570) ∈ (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0621 : (nb078_alpha_dummy_570) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_577) (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_569)) (Wff.classEq (Class.cv (nb078_alpha_dummy_577)) (syn_cphi (Class.cv (nb078_alpha_dummy_578)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_577) (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_570)) (Wff.classEq (Class.cv (nb078_alpha_dummy_577)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_578))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0620) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0620) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0622 (g : Var) : (nb078_alpha_dummy_573 g) ∈ (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0623 (g : Var) : (nb078_alpha_dummy_573 g) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_579 g) (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_572 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_579 g) (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_573 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0622 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0622 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0624 : (nb078_alpha_dummy_570) ∈ (((Class.cab (nb078_alpha_dummy_577) (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_570)) (Wff.classEq (Class.cv (nb078_alpha_dummy_577)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_578))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_577) (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_570)) (Wff.classEq (Class.cv (nb078_alpha_dummy_577)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_578))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0620) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0620) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0625 (g : Var) : (nb078_alpha_dummy_573 g) ∈ (((Class.cab (nb078_alpha_dummy_579 g) (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_573 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_579 g) (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_573 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0622 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0622 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0626 : (nb078_alpha_dummy_578) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_578))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0627 (g : Var) : (nb078_alpha_dummy_580 g) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0628 : (nb078_alpha_dummy_578) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_578)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_578)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0629 (g : Var) : (nb078_alpha_dummy_580 g) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0630 : (nb078_alpha_dummy_569) ∈ (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_571))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0631 : (nb078_alpha_dummy_569) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_613) (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_569)) (Wff.classEq (Class.cv (nb078_alpha_dummy_613)) (syn_cphi (Class.cv (nb078_alpha_dummy_614)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_613) (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_571)) (Wff.classEq (Class.cv (nb078_alpha_dummy_613)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_614))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0630) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0630) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0632 (g : Var) : (nb078_alpha_dummy_572 g) ∈ (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_574 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0633 (g : Var) : (nb078_alpha_dummy_572 g) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_615 g) (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_572 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_615 g) (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_574 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0632 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0632 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0634 : (nb078_alpha_dummy_569) ∈ (((Class.cab (nb078_alpha_dummy_613) (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_569)) (Wff.classEq (Class.cv (nb078_alpha_dummy_613)) (syn_cphi (Class.cv (nb078_alpha_dummy_614))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_613) (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_569)) (Wff.classEq (Class.cv (nb078_alpha_dummy_613)) (syn_cphi (Class.cv (nb078_alpha_dummy_614))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0630) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0630) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0635 (g : Var) : (nb078_alpha_dummy_572 g) ∈ (((Class.cab (nb078_alpha_dummy_615 g) (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_572 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_615 g) (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_572 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0632 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0632 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0636 : (nb078_alpha_dummy_614) ∈ (((Class.cv (nb078_alpha_dummy_614))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0637 (g : Var) : (nb078_alpha_dummy_616 g) ∈ (((Class.cv (nb078_alpha_dummy_616 g))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0638 : (nb078_alpha_dummy_621) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_621)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_621)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_621))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0639 (g : Var) : (nb078_alpha_dummy_623 g) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_623 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_623 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_623 g))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0640 : (nb078_alpha_dummy_621) ∈ (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0641 (g : Var) : (nb078_alpha_dummy_623 g) ∈ (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0642 : (nb078_alpha_dummy_628) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_628)) (Class.cv (nb078_alpha_dummy_629)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_628)) (Class.cv (nb078_alpha_dummy_629)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0643 (g : Var) : (nb078_alpha_dummy_631 g) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_631 g)) (Class.cv (nb078_alpha_dummy_632 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_631 g)) (Class.cv (nb078_alpha_dummy_632 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0644 : (nb078_alpha_dummy_628) ∈ (((Class.cv (nb078_alpha_dummy_628))).fv ∪ ((Class.cv (nb078_alpha_dummy_629))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0645 (g : Var) : (nb078_alpha_dummy_631 g) ∈ (((Class.cv (nb078_alpha_dummy_631 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_632 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0646 : (nb078_alpha_dummy_629) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_628)) (Class.cv (nb078_alpha_dummy_629)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_628)) (Class.cv (nb078_alpha_dummy_629)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0647 (g : Var) : (nb078_alpha_dummy_632 g) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_631 g)) (Class.cv (nb078_alpha_dummy_632 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_631 g)) (Class.cv (nb078_alpha_dummy_632 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0648 : (nb078_alpha_dummy_629) ∈ (((Class.cv (nb078_alpha_dummy_628))).fv ∪ ((Class.cv (nb078_alpha_dummy_629))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0649 (g : Var) : (nb078_alpha_dummy_632 g) ∈ (((Class.cv (nb078_alpha_dummy_631 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_632 g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0650 : (nb078_alpha_dummy_628) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_628)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_629)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0651 (g : Var) : (nb078_alpha_dummy_631 g) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_631 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_632 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0652 : (nb078_alpha_dummy_628) ∈ (((Class.cv (nb078_alpha_dummy_628))).fv ∪ ((Class.cv (nb078_alpha_dummy_628))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0653 (g : Var) : (nb078_alpha_dummy_631 g) ∈ (((Class.cv (nb078_alpha_dummy_631 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_631 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0654 : (nb078_alpha_dummy_629) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_628)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_629)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0655 (g : Var) : (nb078_alpha_dummy_632 g) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_631 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_632 g)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0656 : (nb078_alpha_dummy_629) ∈ (((Class.cv (nb078_alpha_dummy_629))).fv ∪ ((Class.cv (nb078_alpha_dummy_629))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0657 (g : Var) : (nb078_alpha_dummy_632 g) ∈ (((Class.cv (nb078_alpha_dummy_632 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_632 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0658 : (nb078_alpha_dummy_571) ∈ (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_571))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0659 : (nb078_alpha_dummy_571) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_613) (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_569)) (Wff.classEq (Class.cv (nb078_alpha_dummy_613)) (syn_cphi (Class.cv (nb078_alpha_dummy_614)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_613) (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_571)) (Wff.classEq (Class.cv (nb078_alpha_dummy_613)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_614))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0658) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0658) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0660 (g : Var) : (nb078_alpha_dummy_574 g) ∈ (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_574 g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0661 (g : Var) : (nb078_alpha_dummy_574 g) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_615 g) (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_572 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_615 g) (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_574 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0660 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0660 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0662 : (nb078_alpha_dummy_571) ∈ (((Class.cab (nb078_alpha_dummy_613) (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_571)) (Wff.classEq (Class.cv (nb078_alpha_dummy_613)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_614))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_613) (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_571)) (Wff.classEq (Class.cv (nb078_alpha_dummy_613)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_614))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0658) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0658) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0663 (g : Var) : (nb078_alpha_dummy_574 g) ∈ (((Class.cab (nb078_alpha_dummy_615 g) (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_574 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_615 g) (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_574 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0660 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0660 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0664 : (nb078_alpha_dummy_614) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_614))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0665 (g : Var) : (nb078_alpha_dummy_616 g) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0666 : (nb078_alpha_dummy_614) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_614)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_614)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0667 (g : Var) : (nb078_alpha_dummy_616 g) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0668 : (nb078_alpha_dummy_649) ∈ (({(nb078_alpha_dummy_649)} : Finset Var) ∪ ({(nb078_alpha_dummy_650)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_650)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_649)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0669 (g : Var) : (nb078_alpha_dummy_651 g) ∈ (({(nb078_alpha_dummy_651 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_652 g)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_652 g)) (syn_ccnv (Class.cv g)) (Class.cv (nb078_alpha_dummy_651 g)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0670 : (nb078_alpha_dummy_650) ∈ (({(nb078_alpha_dummy_649)} : Finset Var) ∪ ({(nb078_alpha_dummy_650)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_650)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_649)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0671 (g : Var) : (nb078_alpha_dummy_652 g) ∈ (({(nb078_alpha_dummy_651 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_652 g)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_652 g)) (syn_ccnv (Class.cv g)) (Class.cv (nb078_alpha_dummy_651 g)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0672 : (nb078_alpha_dummy_649) ∈ (((Class.cv (nb078_alpha_dummy_649))).fv ∪ ((Class.cv (nb078_alpha_dummy_650))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0673 : (nb078_alpha_dummy_649) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_655) (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_649)) (Wff.classEq (Class.cv (nb078_alpha_dummy_655)) (syn_cphi (Class.cv (nb078_alpha_dummy_656)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_655) (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_650)) (Wff.classEq (Class.cv (nb078_alpha_dummy_655)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_656))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0672) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0672) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0674 (g : Var) : (nb078_alpha_dummy_651 g) ∈ (((Class.cv (nb078_alpha_dummy_651 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_652 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0675 (g : Var) : (nb078_alpha_dummy_651 g) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_657 g) (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_651 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_657 g) (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_652 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0674 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0674 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0676 : (nb078_alpha_dummy_649) ∈ (((Class.cab (nb078_alpha_dummy_655) (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_649)) (Wff.classEq (Class.cv (nb078_alpha_dummy_655)) (syn_cphi (Class.cv (nb078_alpha_dummy_656))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_655) (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_649)) (Wff.classEq (Class.cv (nb078_alpha_dummy_655)) (syn_cphi (Class.cv (nb078_alpha_dummy_656))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0672) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0672) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0677 (g : Var) : (nb078_alpha_dummy_651 g) ∈ (((Class.cab (nb078_alpha_dummy_657 g) (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_651 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_657 g) (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_651 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0674 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0674 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0678 : (nb078_alpha_dummy_656) ∈ (((Class.cv (nb078_alpha_dummy_656))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0679 (g : Var) : (nb078_alpha_dummy_658 g) ∈ (((Class.cv (nb078_alpha_dummy_658 g))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0680 : (nb078_alpha_dummy_663) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_663)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_663)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_663))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0681 (g : Var) : (nb078_alpha_dummy_665 g) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_665 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_665 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_665 g))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0682 : (nb078_alpha_dummy_663) ∈ (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0683 (g : Var) : (nb078_alpha_dummy_665 g) ∈ (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0684 : (nb078_alpha_dummy_670) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_670)) (Class.cv (nb078_alpha_dummy_671)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_670)) (Class.cv (nb078_alpha_dummy_671)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0685 (g : Var) : (nb078_alpha_dummy_673 g) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_673 g)) (Class.cv (nb078_alpha_dummy_674 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_673 g)) (Class.cv (nb078_alpha_dummy_674 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0686 : (nb078_alpha_dummy_670) ∈ (((Class.cv (nb078_alpha_dummy_670))).fv ∪ ((Class.cv (nb078_alpha_dummy_671))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0687 (g : Var) : (nb078_alpha_dummy_673 g) ∈ (((Class.cv (nb078_alpha_dummy_673 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_674 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0688 : (nb078_alpha_dummy_671) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_670)) (Class.cv (nb078_alpha_dummy_671)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_670)) (Class.cv (nb078_alpha_dummy_671)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0689 (g : Var) : (nb078_alpha_dummy_674 g) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_673 g)) (Class.cv (nb078_alpha_dummy_674 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_673 g)) (Class.cv (nb078_alpha_dummy_674 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0690 : (nb078_alpha_dummy_671) ∈ (((Class.cv (nb078_alpha_dummy_670))).fv ∪ ((Class.cv (nb078_alpha_dummy_671))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0691 (g : Var) : (nb078_alpha_dummy_674 g) ∈ (((Class.cv (nb078_alpha_dummy_673 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_674 g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0692 : (nb078_alpha_dummy_670) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_670)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_671)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0693 (g : Var) : (nb078_alpha_dummy_673 g) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_673 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_674 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0694 : (nb078_alpha_dummy_670) ∈ (((Class.cv (nb078_alpha_dummy_670))).fv ∪ ((Class.cv (nb078_alpha_dummy_670))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0695 (g : Var) : (nb078_alpha_dummy_673 g) ∈ (((Class.cv (nb078_alpha_dummy_673 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_673 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0696 : (nb078_alpha_dummy_671) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_670)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_671)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0697 (g : Var) : (nb078_alpha_dummy_674 g) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_673 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_674 g)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0698 : (nb078_alpha_dummy_671) ∈ (((Class.cv (nb078_alpha_dummy_671))).fv ∪ ((Class.cv (nb078_alpha_dummy_671))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0699 (g : Var) : (nb078_alpha_dummy_674 g) ∈ (((Class.cv (nb078_alpha_dummy_674 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_674 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0700 : (nb078_alpha_dummy_650) ∈ (((Class.cv (nb078_alpha_dummy_649))).fv ∪ ((Class.cv (nb078_alpha_dummy_650))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0701 : (nb078_alpha_dummy_650) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_655) (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_649)) (Wff.classEq (Class.cv (nb078_alpha_dummy_655)) (syn_cphi (Class.cv (nb078_alpha_dummy_656)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_655) (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_650)) (Wff.classEq (Class.cv (nb078_alpha_dummy_655)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_656))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0700) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0700) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0702 (g : Var) : (nb078_alpha_dummy_652 g) ∈ (((Class.cv (nb078_alpha_dummy_651 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_652 g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0703 (g : Var) : (nb078_alpha_dummy_652 g) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_657 g) (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_651 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_657 g) (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_652 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0702 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0702 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0704 : (nb078_alpha_dummy_650) ∈ (((Class.cab (nb078_alpha_dummy_655) (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_650)) (Wff.classEq (Class.cv (nb078_alpha_dummy_655)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_656))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_655) (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_650)) (Wff.classEq (Class.cv (nb078_alpha_dummy_655)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_656))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0700) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0700) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0705 (g : Var) : (nb078_alpha_dummy_652 g) ∈ (((Class.cab (nb078_alpha_dummy_657 g) (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_652 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_657 g) (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_652 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0702 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0702 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0706 : (nb078_alpha_dummy_656) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_656))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0707 (g : Var) : (nb078_alpha_dummy_658 g) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0708 : (nb078_alpha_dummy_656) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_656)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_656)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0709 (g : Var) : (nb078_alpha_dummy_658 g) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0710 : (nb078_alpha_dummy_650) ∈ (((Class.cv (nb078_alpha_dummy_650))).fv ∪ ((Class.cv (nb078_alpha_dummy_649))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0711 : (nb078_alpha_dummy_650) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_691) (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_650)) (Wff.classEq (Class.cv (nb078_alpha_dummy_691)) (syn_cphi (Class.cv (nb078_alpha_dummy_692)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_691) (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_649)) (Wff.classEq (Class.cv (nb078_alpha_dummy_691)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_692))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0710) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0710) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0712 (g : Var) : (nb078_alpha_dummy_652 g) ∈ (((Class.cv (nb078_alpha_dummy_652 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_651 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0713 (g : Var) : (nb078_alpha_dummy_652 g) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_693 g) (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_652 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_693 g) (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_651 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0712 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0712 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0714 : (nb078_alpha_dummy_650) ∈ (((Class.cab (nb078_alpha_dummy_691) (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_650)) (Wff.classEq (Class.cv (nb078_alpha_dummy_691)) (syn_cphi (Class.cv (nb078_alpha_dummy_692))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_691) (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_650)) (Wff.classEq (Class.cv (nb078_alpha_dummy_691)) (syn_cphi (Class.cv (nb078_alpha_dummy_692))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0710) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0710) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0715 (g : Var) : (nb078_alpha_dummy_652 g) ∈ (((Class.cab (nb078_alpha_dummy_693 g) (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_652 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_693 g) (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_652 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0712 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0712 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0716 : (nb078_alpha_dummy_692) ∈ (((Class.cv (nb078_alpha_dummy_692))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0717 (g : Var) : (nb078_alpha_dummy_694 g) ∈ (((Class.cv (nb078_alpha_dummy_694 g))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0718 : (nb078_alpha_dummy_699) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_699)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_699)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_699))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0719 (g : Var) : (nb078_alpha_dummy_701 g) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_701 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_701 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_701 g))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0720 : (nb078_alpha_dummy_699) ∈ (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0721 (g : Var) : (nb078_alpha_dummy_701 g) ∈ (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0722 : (nb078_alpha_dummy_706) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_706)) (Class.cv (nb078_alpha_dummy_707)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_706)) (Class.cv (nb078_alpha_dummy_707)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0723 (g : Var) : (nb078_alpha_dummy_709 g) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_709 g)) (Class.cv (nb078_alpha_dummy_710 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_709 g)) (Class.cv (nb078_alpha_dummy_710 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0724 : (nb078_alpha_dummy_706) ∈ (((Class.cv (nb078_alpha_dummy_706))).fv ∪ ((Class.cv (nb078_alpha_dummy_707))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0725 (g : Var) : (nb078_alpha_dummy_709 g) ∈ (((Class.cv (nb078_alpha_dummy_709 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_710 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0726 : (nb078_alpha_dummy_707) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_706)) (Class.cv (nb078_alpha_dummy_707)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_706)) (Class.cv (nb078_alpha_dummy_707)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0727 (g : Var) : (nb078_alpha_dummy_710 g) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_709 g)) (Class.cv (nb078_alpha_dummy_710 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_709 g)) (Class.cv (nb078_alpha_dummy_710 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0728 : (nb078_alpha_dummy_707) ∈ (((Class.cv (nb078_alpha_dummy_706))).fv ∪ ((Class.cv (nb078_alpha_dummy_707))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0729 (g : Var) : (nb078_alpha_dummy_710 g) ∈ (((Class.cv (nb078_alpha_dummy_709 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_710 g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0730 : (nb078_alpha_dummy_706) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_706)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_707)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0731 (g : Var) : (nb078_alpha_dummy_709 g) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_709 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_710 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0732 : (nb078_alpha_dummy_706) ∈ (((Class.cv (nb078_alpha_dummy_706))).fv ∪ ((Class.cv (nb078_alpha_dummy_706))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0733 (g : Var) : (nb078_alpha_dummy_709 g) ∈ (((Class.cv (nb078_alpha_dummy_709 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_709 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0734 : (nb078_alpha_dummy_707) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_706)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_707)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0735 (g : Var) : (nb078_alpha_dummy_710 g) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_709 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_710 g)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0736 : (nb078_alpha_dummy_707) ∈ (((Class.cv (nb078_alpha_dummy_707))).fv ∪ ((Class.cv (nb078_alpha_dummy_707))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0737 (g : Var) : (nb078_alpha_dummy_710 g) ∈ (((Class.cv (nb078_alpha_dummy_710 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_710 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0738 : (nb078_alpha_dummy_649) ∈ (((Class.cv (nb078_alpha_dummy_650))).fv ∪ ((Class.cv (nb078_alpha_dummy_649))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0739 : (nb078_alpha_dummy_649) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_691) (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_650)) (Wff.classEq (Class.cv (nb078_alpha_dummy_691)) (syn_cphi (Class.cv (nb078_alpha_dummy_692)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_691) (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_649)) (Wff.classEq (Class.cv (nb078_alpha_dummy_691)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_692))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
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

theorem nb078_support_mem_0740 (g : Var) : (nb078_alpha_dummy_651 g) ∈ (((Class.cv (nb078_alpha_dummy_652 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_651 g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
