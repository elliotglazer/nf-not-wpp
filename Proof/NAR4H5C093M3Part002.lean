import NAR4H5C093M3Part001

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

theorem nb093_support_mem_0051 (r : Var) : r ∈ (((Class.cv r)).fv ∪ ((syn_ccompl (syn_ccnv (Class.cv r)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0052 (A : Class) : (nb093_alpha_dummy_058 A) ∈ (({(nb093_alpha_dummy_058 A)} : Finset Var) ∪ ({(nb093_alpha_dummy_059 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb093_alpha_dummy_059 A)) (Class.cv (nb093_alpha_dummy_001 A)) (Class.cv (nb093_alpha_dummy_058 A)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0053 (r : Var) : (nb093_alpha_dummy_060 r) ∈ (({(nb093_alpha_dummy_060 r)} : Finset Var) ∪ ({(nb093_alpha_dummy_061 r)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb093_alpha_dummy_061 r)) (Class.cv r) (Class.cv (nb093_alpha_dummy_060 r)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0054 (A : Class) : (nb093_alpha_dummy_059 A) ∈ (({(nb093_alpha_dummy_058 A)} : Finset Var) ∪ ({(nb093_alpha_dummy_059 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb093_alpha_dummy_059 A)) (Class.cv (nb093_alpha_dummy_001 A)) (Class.cv (nb093_alpha_dummy_058 A)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0055 (r : Var) : (nb093_alpha_dummy_061 r) ∈ (({(nb093_alpha_dummy_060 r)} : Finset Var) ∪ ({(nb093_alpha_dummy_061 r)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb093_alpha_dummy_061 r)) (Class.cv r) (Class.cv (nb093_alpha_dummy_060 r)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0056 (A : Class) : (nb093_alpha_dummy_058 A) ∈ (((Class.cv (nb093_alpha_dummy_058 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_059 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0057 (A : Class) : (nb093_alpha_dummy_058 A) ∈ (((syn_ccompl (Class.cab (nb093_alpha_dummy_064 A) (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_058 A)) (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A)) (syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb093_alpha_dummy_064 A) (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_059 A)) (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_065 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0056 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0056 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0058 (r : Var) : (nb093_alpha_dummy_060 r) ∈ (((Class.cv (nb093_alpha_dummy_060 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_061 r))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0059 (r : Var) : (nb093_alpha_dummy_060 r) ∈ (((syn_ccompl (Class.cab (nb093_alpha_dummy_066 r) (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_060 r)) (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r)) (syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))))))).fv ∪ ((syn_ccompl (Class.cab (nb093_alpha_dummy_066 r) (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_061 r)) (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_067 r))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0058 r) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0058 r) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0060 (A : Class) : (nb093_alpha_dummy_058 A) ∈ (((Class.cab (nb093_alpha_dummy_064 A) (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_058 A)) (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A)) (syn_cphi (Class.cv (nb093_alpha_dummy_065 A))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_064 A) (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_058 A)) (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A)) (syn_cphi (Class.cv (nb093_alpha_dummy_065 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0056 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0056 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0061 (r : Var) : (nb093_alpha_dummy_060 r) ∈ (((Class.cab (nb093_alpha_dummy_066 r) (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_060 r)) (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r)) (syn_cphi (Class.cv (nb093_alpha_dummy_067 r))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_066 r) (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_060 r)) (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r)) (syn_cphi (Class.cv (nb093_alpha_dummy_067 r))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0058 r) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0058 r) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0062 (A : Class) : (nb093_alpha_dummy_065 A) ∈ (((Class.cv (nb093_alpha_dummy_065 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0063 (r : Var) : (nb093_alpha_dummy_067 r) ∈ (((Class.cv (nb093_alpha_dummy_067 r))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0064 (A : Class) : (nb093_alpha_dummy_072 A) ∈ (((Wff.classMem (Class.cv (nb093_alpha_dummy_072 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb093_alpha_dummy_072 A)) (syn_c1c))).fv ∪ ((Class.cv (nb093_alpha_dummy_072 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0065 (r : Var) : (nb093_alpha_dummy_074 r) ∈ (((Wff.classMem (Class.cv (nb093_alpha_dummy_074 r)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb093_alpha_dummy_074 r)) (syn_c1c))).fv ∪ ((Class.cv (nb093_alpha_dummy_074 r))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0066 (A : Class) : (nb093_alpha_dummy_072 A) ∈ (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0067 (r : Var) : (nb093_alpha_dummy_074 r) ∈ (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0068 (A : Class) : (nb093_alpha_dummy_079 A) ∈ (((syn_cnin (Class.cv (nb093_alpha_dummy_079 A)) (Class.cv (nb093_alpha_dummy_080 A)))).fv ∪ ((syn_cnin (Class.cv (nb093_alpha_dummy_079 A)) (Class.cv (nb093_alpha_dummy_080 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0069 (r : Var) : (nb093_alpha_dummy_082 r) ∈ (((syn_cnin (Class.cv (nb093_alpha_dummy_082 r)) (Class.cv (nb093_alpha_dummy_083 r)))).fv ∪ ((syn_cnin (Class.cv (nb093_alpha_dummy_082 r)) (Class.cv (nb093_alpha_dummy_083 r)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0070 (A : Class) : (nb093_alpha_dummy_079 A) ∈ (((Class.cv (nb093_alpha_dummy_079 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_080 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0071 (r : Var) : (nb093_alpha_dummy_082 r) ∈ (((Class.cv (nb093_alpha_dummy_082 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_083 r))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0072 (A : Class) : (nb093_alpha_dummy_080 A) ∈ (((syn_cnin (Class.cv (nb093_alpha_dummy_079 A)) (Class.cv (nb093_alpha_dummy_080 A)))).fv ∪ ((syn_cnin (Class.cv (nb093_alpha_dummy_079 A)) (Class.cv (nb093_alpha_dummy_080 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0073 (r : Var) : (nb093_alpha_dummy_083 r) ∈ (((syn_cnin (Class.cv (nb093_alpha_dummy_082 r)) (Class.cv (nb093_alpha_dummy_083 r)))).fv ∪ ((syn_cnin (Class.cv (nb093_alpha_dummy_082 r)) (Class.cv (nb093_alpha_dummy_083 r)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0074 (A : Class) : (nb093_alpha_dummy_080 A) ∈ (((Class.cv (nb093_alpha_dummy_079 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_080 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0075 (r : Var) : (nb093_alpha_dummy_083 r) ∈ (((Class.cv (nb093_alpha_dummy_082 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_083 r))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0076 (A : Class) : (nb093_alpha_dummy_079 A) ∈ (((syn_ccompl (Class.cv (nb093_alpha_dummy_079 A)))).fv ∪ ((syn_ccompl (Class.cv (nb093_alpha_dummy_080 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0077 (r : Var) : (nb093_alpha_dummy_082 r) ∈ (((syn_ccompl (Class.cv (nb093_alpha_dummy_082 r)))).fv ∪ ((syn_ccompl (Class.cv (nb093_alpha_dummy_083 r)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0078 (A : Class) : (nb093_alpha_dummy_079 A) ∈ (((Class.cv (nb093_alpha_dummy_079 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_079 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0079 (r : Var) : (nb093_alpha_dummy_082 r) ∈ (((Class.cv (nb093_alpha_dummy_082 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_082 r))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0080 (A : Class) : (nb093_alpha_dummy_080 A) ∈ (((syn_ccompl (Class.cv (nb093_alpha_dummy_079 A)))).fv ∪ ((syn_ccompl (Class.cv (nb093_alpha_dummy_080 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0081 (r : Var) : (nb093_alpha_dummy_083 r) ∈ (((syn_ccompl (Class.cv (nb093_alpha_dummy_082 r)))).fv ∪ ((syn_ccompl (Class.cv (nb093_alpha_dummy_083 r)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0082 (A : Class) : (nb093_alpha_dummy_080 A) ∈ (((Class.cv (nb093_alpha_dummy_080 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_080 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0083 (r : Var) : (nb093_alpha_dummy_083 r) ∈ (((Class.cv (nb093_alpha_dummy_083 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_083 r))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0084 (A : Class) : (nb093_alpha_dummy_059 A) ∈ (((Class.cv (nb093_alpha_dummy_058 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_059 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0085 (A : Class) : (nb093_alpha_dummy_059 A) ∈ (((syn_ccompl (Class.cab (nb093_alpha_dummy_064 A) (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_058 A)) (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A)) (syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb093_alpha_dummy_064 A) (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_059 A)) (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_065 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0084 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0084 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0086 (r : Var) : (nb093_alpha_dummy_061 r) ∈ (((Class.cv (nb093_alpha_dummy_060 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_061 r))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0087 (r : Var) : (nb093_alpha_dummy_061 r) ∈ (((syn_ccompl (Class.cab (nb093_alpha_dummy_066 r) (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_060 r)) (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r)) (syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))))))).fv ∪ ((syn_ccompl (Class.cab (nb093_alpha_dummy_066 r) (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_061 r)) (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_067 r))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0086 r) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0086 r) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0088 (A : Class) : (nb093_alpha_dummy_059 A) ∈ (((Class.cab (nb093_alpha_dummy_064 A) (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_059 A)) (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_065 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_064 A) (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_059 A)) (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_065 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0084 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0084 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0089 (r : Var) : (nb093_alpha_dummy_061 r) ∈ (((Class.cab (nb093_alpha_dummy_066 r) (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_061 r)) (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_067 r))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_066 r) (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_061 r)) (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_067 r))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0086 r) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0086 r) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0090 (A : Class) : (nb093_alpha_dummy_065 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_065 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0091 (r : Var) : (nb093_alpha_dummy_067 r) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_067 r))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0092 (A : Class) : (nb093_alpha_dummy_065 A) ∈ (((syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))).fv ∪ ((syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0093 (r : Var) : (nb093_alpha_dummy_067 r) ∈ (((syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))).fv ∪ ((syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0094 (A : Class) : (nb093_alpha_dummy_059 A) ∈ (((Class.cv (nb093_alpha_dummy_059 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_058 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0095 (A : Class) : (nb093_alpha_dummy_059 A) ∈ (((syn_ccompl (Class.cab (nb093_alpha_dummy_100 A) (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_059 A)) (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A)) (syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb093_alpha_dummy_100 A) (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_058 A)) (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_101 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0094 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0094 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0096 (r : Var) : (nb093_alpha_dummy_061 r) ∈ (((Class.cv (nb093_alpha_dummy_061 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_060 r))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0097 (r : Var) : (nb093_alpha_dummy_061 r) ∈ (((syn_ccompl (Class.cab (nb093_alpha_dummy_102 r) (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_061 r)) (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r)) (syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))))))).fv ∪ ((syn_ccompl (Class.cab (nb093_alpha_dummy_102 r) (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_060 r)) (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_103 r))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0096 r) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0096 r) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0098 (A : Class) : (nb093_alpha_dummy_059 A) ∈ (((Class.cab (nb093_alpha_dummy_100 A) (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_059 A)) (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A)) (syn_cphi (Class.cv (nb093_alpha_dummy_101 A))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_100 A) (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_059 A)) (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A)) (syn_cphi (Class.cv (nb093_alpha_dummy_101 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0094 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0094 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0099 (r : Var) : (nb093_alpha_dummy_061 r) ∈ (((Class.cab (nb093_alpha_dummy_102 r) (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_061 r)) (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r)) (syn_cphi (Class.cv (nb093_alpha_dummy_103 r))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_102 r) (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_061 r)) (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r)) (syn_cphi (Class.cv (nb093_alpha_dummy_103 r))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0096 r) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0096 r) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0100 (A : Class) : (nb093_alpha_dummy_101 A) ∈ (((Class.cv (nb093_alpha_dummy_101 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0101 (r : Var) : (nb093_alpha_dummy_103 r) ∈ (((Class.cv (nb093_alpha_dummy_103 r))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0102 (A : Class) : (nb093_alpha_dummy_108 A) ∈ (((Wff.classMem (Class.cv (nb093_alpha_dummy_108 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb093_alpha_dummy_108 A)) (syn_c1c))).fv ∪ ((Class.cv (nb093_alpha_dummy_108 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0103 (r : Var) : (nb093_alpha_dummy_110 r) ∈ (((Wff.classMem (Class.cv (nb093_alpha_dummy_110 r)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb093_alpha_dummy_110 r)) (syn_c1c))).fv ∪ ((Class.cv (nb093_alpha_dummy_110 r))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0104 (A : Class) : (nb093_alpha_dummy_108 A) ∈ (((Class.cv (nb093_alpha_dummy_108 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0105 (r : Var) : (nb093_alpha_dummy_110 r) ∈ (((Class.cv (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0106 (A : Class) : (nb093_alpha_dummy_115 A) ∈ (((syn_cnin (Class.cv (nb093_alpha_dummy_115 A)) (Class.cv (nb093_alpha_dummy_116 A)))).fv ∪ ((syn_cnin (Class.cv (nb093_alpha_dummy_115 A)) (Class.cv (nb093_alpha_dummy_116 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0107 (r : Var) : (nb093_alpha_dummy_118 r) ∈ (((syn_cnin (Class.cv (nb093_alpha_dummy_118 r)) (Class.cv (nb093_alpha_dummy_119 r)))).fv ∪ ((syn_cnin (Class.cv (nb093_alpha_dummy_118 r)) (Class.cv (nb093_alpha_dummy_119 r)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0108 (A : Class) : (nb093_alpha_dummy_115 A) ∈ (((Class.cv (nb093_alpha_dummy_115 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_116 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0109 (r : Var) : (nb093_alpha_dummy_118 r) ∈ (((Class.cv (nb093_alpha_dummy_118 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_119 r))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0110 (A : Class) : (nb093_alpha_dummy_116 A) ∈ (((syn_cnin (Class.cv (nb093_alpha_dummy_115 A)) (Class.cv (nb093_alpha_dummy_116 A)))).fv ∪ ((syn_cnin (Class.cv (nb093_alpha_dummy_115 A)) (Class.cv (nb093_alpha_dummy_116 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0111 (r : Var) : (nb093_alpha_dummy_119 r) ∈ (((syn_cnin (Class.cv (nb093_alpha_dummy_118 r)) (Class.cv (nb093_alpha_dummy_119 r)))).fv ∪ ((syn_cnin (Class.cv (nb093_alpha_dummy_118 r)) (Class.cv (nb093_alpha_dummy_119 r)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0112 (A : Class) : (nb093_alpha_dummy_116 A) ∈ (((Class.cv (nb093_alpha_dummy_115 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_116 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0113 (r : Var) : (nb093_alpha_dummy_119 r) ∈ (((Class.cv (nb093_alpha_dummy_118 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_119 r))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0114 (A : Class) : (nb093_alpha_dummy_115 A) ∈ (((syn_ccompl (Class.cv (nb093_alpha_dummy_115 A)))).fv ∪ ((syn_ccompl (Class.cv (nb093_alpha_dummy_116 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0115 (r : Var) : (nb093_alpha_dummy_118 r) ∈ (((syn_ccompl (Class.cv (nb093_alpha_dummy_118 r)))).fv ∪ ((syn_ccompl (Class.cv (nb093_alpha_dummy_119 r)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0116 (A : Class) : (nb093_alpha_dummy_115 A) ∈ (((Class.cv (nb093_alpha_dummy_115 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_115 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0117 (r : Var) : (nb093_alpha_dummy_118 r) ∈ (((Class.cv (nb093_alpha_dummy_118 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_118 r))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0118 (A : Class) : (nb093_alpha_dummy_116 A) ∈ (((syn_ccompl (Class.cv (nb093_alpha_dummy_115 A)))).fv ∪ ((syn_ccompl (Class.cv (nb093_alpha_dummy_116 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0119 (r : Var) : (nb093_alpha_dummy_119 r) ∈ (((syn_ccompl (Class.cv (nb093_alpha_dummy_118 r)))).fv ∪ ((syn_ccompl (Class.cv (nb093_alpha_dummy_119 r)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0120 (A : Class) : (nb093_alpha_dummy_116 A) ∈ (((Class.cv (nb093_alpha_dummy_116 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_116 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0121 (r : Var) : (nb093_alpha_dummy_119 r) ∈ (((Class.cv (nb093_alpha_dummy_119 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_119 r))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0122 (A : Class) : (nb093_alpha_dummy_058 A) ∈ (((Class.cv (nb093_alpha_dummy_059 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_058 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0123 (A : Class) : (nb093_alpha_dummy_058 A) ∈ (((syn_ccompl (Class.cab (nb093_alpha_dummy_100 A) (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_059 A)) (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A)) (syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb093_alpha_dummy_100 A) (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_058 A)) (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_101 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0122 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0122 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0124 (r : Var) : (nb093_alpha_dummy_060 r) ∈ (((Class.cv (nb093_alpha_dummy_061 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_060 r))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0125 (r : Var) : (nb093_alpha_dummy_060 r) ∈ (((syn_ccompl (Class.cab (nb093_alpha_dummy_102 r) (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_061 r)) (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r)) (syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))))))).fv ∪ ((syn_ccompl (Class.cab (nb093_alpha_dummy_102 r) (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_060 r)) (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_103 r))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0124 r) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0124 r) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0126 (A : Class) : (nb093_alpha_dummy_058 A) ∈ (((Class.cab (nb093_alpha_dummy_100 A) (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_058 A)) (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_101 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_100 A) (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_058 A)) (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_101 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0122 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0122 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0127 (r : Var) : (nb093_alpha_dummy_060 r) ∈ (((Class.cab (nb093_alpha_dummy_102 r) (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_060 r)) (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_103 r))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_102 r) (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_060 r)) (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_103 r))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0124 r) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0124 r) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0128 (A : Class) : (nb093_alpha_dummy_101 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_101 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0129 (r : Var) : (nb093_alpha_dummy_103 r) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_103 r))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0130 (A : Class) : (nb093_alpha_dummy_101 A) ∈ (((syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))).fv ∪ ((syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0131 (r : Var) : (nb093_alpha_dummy_103 r) ∈ (((syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))).fv ∪ ((syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0132 (A : Class) : (nb093_alpha_dummy_001 A) ∈ (((syn_ccnv (Class.cv (nb093_alpha_dummy_001 A)))).fv ∪ ((syn_ccnv (Class.cv (nb093_alpha_dummy_001 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0133 (r : Var) : r ∈ (((syn_ccnv (Class.cv r))).fv ∪ ((syn_ccnv (Class.cv r))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0134 (A : Class) : (nb093_alpha_dummy_001 A) ∈ (({(nb093_alpha_dummy_058 A)} : Finset Var) ∪ ({(nb093_alpha_dummy_059 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb093_alpha_dummy_059 A)) (Class.cv (nb093_alpha_dummy_001 A)) (Class.cv (nb093_alpha_dummy_058 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0135 (r : Var) : r ∈ (({(nb093_alpha_dummy_060 r)} : Finset Var) ∪ ({(nb093_alpha_dummy_061 r)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb093_alpha_dummy_061 r)) (Class.cv r) (Class.cv (nb093_alpha_dummy_060 r)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0136 (A : Class) : (nb093_alpha_dummy_001 A) ∈ (((Class.cv (nb093_alpha_dummy_001 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0137 (r : Var) : r ∈ (((Class.cv r)).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0138 (A : Class) : (nb093_alpha_dummy_045 A) ∈ (((Class.cv (nb093_alpha_dummy_045 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0139 (r : Var) (d : Var) : (nb093_alpha_dummy_047 r d) ∈ (((Class.cv (nb093_alpha_dummy_047 r d))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0140 (A : Class) : (nb093_alpha_dummy_136 A) ∈ (((Wff.classMem (Class.cv (nb093_alpha_dummy_136 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb093_alpha_dummy_136 A)) (syn_c1c))).fv ∪ ((Class.cv (nb093_alpha_dummy_136 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0141 (r : Var) (d : Var) : (nb093_alpha_dummy_138 r d) ∈ (((Wff.classMem (Class.cv (nb093_alpha_dummy_138 r d)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb093_alpha_dummy_138 r d)) (syn_c1c))).fv ∪ ((Class.cv (nb093_alpha_dummy_138 r d))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0142 (A : Class) : (nb093_alpha_dummy_136 A) ∈ (((Class.cv (nb093_alpha_dummy_136 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0143 (r : Var) (d : Var) : (nb093_alpha_dummy_138 r d) ∈ (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0144 (A : Class) : (nb093_alpha_dummy_143 A) ∈ (((syn_cnin (Class.cv (nb093_alpha_dummy_143 A)) (Class.cv (nb093_alpha_dummy_144 A)))).fv ∪ ((syn_cnin (Class.cv (nb093_alpha_dummy_143 A)) (Class.cv (nb093_alpha_dummy_144 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0145 (r : Var) (d : Var) : (nb093_alpha_dummy_146 r d) ∈ (((syn_cnin (Class.cv (nb093_alpha_dummy_146 r d)) (Class.cv (nb093_alpha_dummy_147 r d)))).fv ∪ ((syn_cnin (Class.cv (nb093_alpha_dummy_146 r d)) (Class.cv (nb093_alpha_dummy_147 r d)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0146 (A : Class) : (nb093_alpha_dummy_143 A) ∈ (((Class.cv (nb093_alpha_dummy_143 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_144 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0147 (r : Var) (d : Var) : (nb093_alpha_dummy_146 r d) ∈ (((Class.cv (nb093_alpha_dummy_146 r d))).fv ∪ ((Class.cv (nb093_alpha_dummy_147 r d))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0148 (A : Class) : (nb093_alpha_dummy_144 A) ∈ (((syn_cnin (Class.cv (nb093_alpha_dummy_143 A)) (Class.cv (nb093_alpha_dummy_144 A)))).fv ∪ ((syn_cnin (Class.cv (nb093_alpha_dummy_143 A)) (Class.cv (nb093_alpha_dummy_144 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0149 (r : Var) (d : Var) : (nb093_alpha_dummy_147 r d) ∈ (((syn_cnin (Class.cv (nb093_alpha_dummy_146 r d)) (Class.cv (nb093_alpha_dummy_147 r d)))).fv ∪ ((syn_cnin (Class.cv (nb093_alpha_dummy_146 r d)) (Class.cv (nb093_alpha_dummy_147 r d)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0150 (A : Class) : (nb093_alpha_dummy_144 A) ∈ (((Class.cv (nb093_alpha_dummy_143 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_144 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0151 (r : Var) (d : Var) : (nb093_alpha_dummy_147 r d) ∈ (((Class.cv (nb093_alpha_dummy_146 r d))).fv ∪ ((Class.cv (nb093_alpha_dummy_147 r d))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0152 (A : Class) : (nb093_alpha_dummy_143 A) ∈ (((syn_ccompl (Class.cv (nb093_alpha_dummy_143 A)))).fv ∪ ((syn_ccompl (Class.cv (nb093_alpha_dummy_144 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0153 (r : Var) (d : Var) : (nb093_alpha_dummy_146 r d) ∈ (((syn_ccompl (Class.cv (nb093_alpha_dummy_146 r d)))).fv ∪ ((syn_ccompl (Class.cv (nb093_alpha_dummy_147 r d)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0154 (A : Class) : (nb093_alpha_dummy_143 A) ∈ (((Class.cv (nb093_alpha_dummy_143 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_143 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0155 (r : Var) (d : Var) : (nb093_alpha_dummy_146 r d) ∈ (((Class.cv (nb093_alpha_dummy_146 r d))).fv ∪ ((Class.cv (nb093_alpha_dummy_146 r d))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0156 (A : Class) : (nb093_alpha_dummy_144 A) ∈ (((syn_ccompl (Class.cv (nb093_alpha_dummy_143 A)))).fv ∪ ((syn_ccompl (Class.cv (nb093_alpha_dummy_144 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0157 (r : Var) (d : Var) : (nb093_alpha_dummy_147 r d) ∈ (((syn_ccompl (Class.cv (nb093_alpha_dummy_146 r d)))).fv ∪ ((syn_ccompl (Class.cv (nb093_alpha_dummy_147 r d)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0158 (A : Class) : (nb093_alpha_dummy_144 A) ∈ (((Class.cv (nb093_alpha_dummy_144 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_144 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0159 (r : Var) (d : Var) : (nb093_alpha_dummy_147 r d) ∈ (((Class.cv (nb093_alpha_dummy_147 r d))).fv ∪ ((Class.cv (nb093_alpha_dummy_147 r d))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0160 (A : Class) : (nb093_alpha_dummy_000 A) ∈ (((syn_cdif (Class.cv (nb093_alpha_dummy_001 A)) (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))).fv ∪ ((Class.cv (nb093_alpha_dummy_000 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0161 (A : Class) : (nb093_alpha_dummy_000 A) ∈ (((syn_ccompl (Class.cab (nb093_alpha_dummy_044 A) (syn_wrex (nb093_alpha_dummy_045 A) (syn_cdif (Class.cv (nb093_alpha_dummy_001 A)) (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A)))) (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A)) (syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb093_alpha_dummy_044 A) (syn_wrex (nb093_alpha_dummy_045 A) (Class.cv (nb093_alpha_dummy_000 A)) (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_045 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0160 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0160 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0162 (r : Var) (d : Var) : d ∈ (((syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))).fv ∪ ((Class.cv d)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0163 (r : Var) (d : Var) : d ∈ (((syn_ccompl (Class.cab (nb093_alpha_dummy_046 r d) (syn_wrex (nb093_alpha_dummy_047 r d) (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r))) (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d)) (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))))))).fv ∪ ((syn_ccompl (Class.cab (nb093_alpha_dummy_046 r d) (syn_wrex (nb093_alpha_dummy_047 r d) (Class.cv d) (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0162 r d) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0162 r d) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0164 (A : Class) : (nb093_alpha_dummy_000 A) ∈ (((Class.cab (nb093_alpha_dummy_044 A) (syn_wrex (nb093_alpha_dummy_045 A) (Class.cv (nb093_alpha_dummy_000 A)) (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_045 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_044 A) (syn_wrex (nb093_alpha_dummy_045 A) (Class.cv (nb093_alpha_dummy_000 A)) (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_045 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0160 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0160 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0165 (r : Var) (d : Var) : d ∈ (((Class.cab (nb093_alpha_dummy_046 r d) (syn_wrex (nb093_alpha_dummy_047 r d) (Class.cv d) (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_046 r d) (syn_wrex (nb093_alpha_dummy_047 r d) (Class.cv d) (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0162 r d) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0162 r d) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0166 (A : Class) : (nb093_alpha_dummy_045 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_045 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0167 (r : Var) (d : Var) : (nb093_alpha_dummy_047 r d) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0168 (A : Class) : (nb093_alpha_dummy_045 A) ∈ (((syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))).fv ∪ ((syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0169 (r : Var) (d : Var) : (nb093_alpha_dummy_047 r d) ∈ (((syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))).fv ∪ ((syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_focused_notmem_0000 (A : Class) : (nb093_alpha_dummy_004 A) ∉ A.fv := by
  change freshVar (((syn_clntpc A)).fv ∪ ((syn_copab (nb093_alpha_dummy_001 A) (nb093_alpha_dummy_000 A) (syn_wbr (syn_cdif (Class.cv (nb093_alpha_dummy_001 A)) (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A)))) (syn_cfound) (Class.cv (nb093_alpha_dummy_000 A))))).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_left _ (((fv_syn_clntpc A).symm ▸ (hu))))

theorem nb093_wpp_notmem_0000 (A : Class) : (nb093_alpha_dummy_004 A) ∉ ((syn_clntpc A)).fv := by
  simpa only [nb093_alpha_dummy_004, fv_syn_clntpc] using (nb093_focused_notmem_0000 A)

theorem nb093_focused_notmem_0001 (A : Class) (r : Var) (d : Var) : (nb093_alpha_dummy_005 A r d) ∉ A.fv := by
  change freshVar (((syn_clntpc A)).fv ∪ ((syn_copab r d (syn_wbr (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r))) (syn_cfound) (Class.cv d)))).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_left _ (((fv_syn_clntpc A).symm ▸ (hu))))

theorem nb093_wpp_notmem_0001 (A : Class) (r : Var) (d : Var) : (nb093_alpha_dummy_005 A r d) ∉ ((syn_clntpc A)).fv := by
  simpa only [nb093_alpha_dummy_005, fv_syn_clntpc] using (nb093_focused_notmem_0001 A r d)

theorem nb093_focused_notmem_0002 (A : Class) : (nb093_alpha_dummy_002 A) ∉ A.fv := by
  change freshVar (((syn_cnin (syn_clntpc A) (syn_copab (nb093_alpha_dummy_001 A) (nb093_alpha_dummy_000 A) (syn_wbr (syn_cdif (Class.cv (nb093_alpha_dummy_001 A)) (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A)))) (syn_cfound) (Class.cv (nb093_alpha_dummy_000 A)))))).fv ∪ ((syn_cnin (syn_clntpc A) (syn_copab (nb093_alpha_dummy_001 A) (nb093_alpha_dummy_000 A) (syn_wbr (syn_cdif (Class.cv (nb093_alpha_dummy_001 A)) (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A)))) (syn_cfound) (Class.cv (nb093_alpha_dummy_000 A)))))).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_left _ (((fv_syn_cnin (syn_clntpc A) (syn_copab (nb093_alpha_dummy_001 A) (nb093_alpha_dummy_000 A) (syn_wbr (syn_cdif (Class.cv (nb093_alpha_dummy_001 A)) (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A)))) (syn_cfound) (Class.cv (nb093_alpha_dummy_000 A))))).symm ▸ (Finset.mem_union_left _ (((fv_syn_clntpc A).symm ▸ (hu)))))))

theorem nb093_wpp_notmem_0002 (A : Class) : (nb093_alpha_dummy_002 A) ∉ ((syn_clntpc A)).fv := by
  simpa only [nb093_alpha_dummy_002, fv_syn_clntpc] using (nb093_focused_notmem_0002 A)

theorem nb093_focused_notmem_0003 (A : Class) (r : Var) (d : Var) : (nb093_alpha_dummy_003 A r d) ∉ A.fv := by
  change freshVar (((syn_cnin (syn_clntpc A) (syn_copab r d (syn_wbr (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r))) (syn_cfound) (Class.cv d))))).fv ∪ ((syn_cnin (syn_clntpc A) (syn_copab r d (syn_wbr (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r))) (syn_cfound) (Class.cv d))))).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_left _ (((fv_syn_cnin (syn_clntpc A) (syn_copab r d (syn_wbr (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r))) (syn_cfound) (Class.cv d)))).symm ▸ (Finset.mem_union_left _ (((fv_syn_clntpc A).symm ▸ (hu)))))))

theorem nb093_wpp_notmem_0003 (A : Class) (r : Var) (d : Var) : (nb093_alpha_dummy_003 A r d) ∉ ((syn_clntpc A)).fv := by
  simpa only [nb093_alpha_dummy_003, fv_syn_clntpc] using (nb093_focused_notmem_0003 A r d)

theorem nb093_compact_envfresh_0000 (A : Class) (r : Var) (d : Var) : TEnvFresh [((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_clntpc A)).fv := by
  exact (TEnvFresh.consFresh (nb093_alpha_dummy_004 A) (nb093_alpha_dummy_005 A r d) (nb093_wpp_notmem_0000 A) (nb093_wpp_notmem_0001 A r d) (TEnvFresh.consFresh (nb093_alpha_dummy_002 A) (nb093_alpha_dummy_003 A r d) (nb093_wpp_notmem_0002 A) (nb093_wpp_notmem_0003 A r d) (TEnvFresh.nil ((syn_clntpc A)).fv)))

noncomputable def nb093_wpp_refl_0000 (A : Class) (r : Var) (d : Var) : TReflOn [((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_clntpc A)).fv :=
  TEnvFresh.reflOn (nb093_compact_envfresh_0000 A r d)

theorem nb093_compact_fv_empty_0000 (A : Class) : (nb093_alpha_dummy_024 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0004 (A : Class) : (nb093_alpha_dummy_024 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_024, fv_syn_c1c] using (nb093_compact_fv_empty_0000 A)

theorem nb093_compact_fv_empty_0001 (r : Var) (d : Var) : (nb093_alpha_dummy_027 r d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0005 (r : Var) (d : Var) : (nb093_alpha_dummy_027 r d) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_027, fv_syn_c1c] using (nb093_compact_fv_empty_0001 r d)

theorem nb093_compact_fv_empty_0002 (A : Class) : (nb093_alpha_dummy_023 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0006 (A : Class) : (nb093_alpha_dummy_023 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_023, fv_syn_c1c] using (nb093_compact_fv_empty_0002 A)

theorem nb093_compact_fv_empty_0003 (r : Var) (d : Var) : (nb093_alpha_dummy_026 r d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0007 (r : Var) (d : Var) : (nb093_alpha_dummy_026 r d) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_026, fv_syn_c1c] using (nb093_compact_fv_empty_0003 r d)

theorem nb093_compact_fv_empty_0004 (A : Class) : (nb093_alpha_dummy_022 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0008 (A : Class) : (nb093_alpha_dummy_022 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_022, fv_syn_c1c] using (nb093_compact_fv_empty_0004 A)

theorem nb093_compact_fv_empty_0005 (r : Var) (d : Var) : (nb093_alpha_dummy_025 r d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0009 (r : Var) (d : Var) : (nb093_alpha_dummy_025 r d) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_025, fv_syn_c1c] using (nb093_compact_fv_empty_0005 r d)

theorem nb093_compact_fv_empty_0006 (A : Class) : (nb093_alpha_dummy_020 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0010 (A : Class) : (nb093_alpha_dummy_020 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_020, fv_syn_c1c] using (nb093_compact_fv_empty_0006 A)

theorem nb093_compact_fv_empty_0007 (r : Var) (d : Var) : (nb093_alpha_dummy_021 r d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0011 (r : Var) (d : Var) : (nb093_alpha_dummy_021 r d) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_021, fv_syn_c1c] using (nb093_compact_fv_empty_0007 r d)

theorem nb093_compact_fv_empty_0008 (A : Class) : (nb093_alpha_dummy_016 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0012 (A : Class) : (nb093_alpha_dummy_016 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_016, fv_syn_c1c] using (nb093_compact_fv_empty_0008 A)

theorem nb093_compact_fv_empty_0009 (r : Var) (d : Var) : (nb093_alpha_dummy_018 r d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0013 (r : Var) (d : Var) : (nb093_alpha_dummy_018 r d) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_018, fv_syn_c1c] using (nb093_compact_fv_empty_0009 r d)

theorem nb093_compact_fv_empty_0010 (A : Class) : (nb093_alpha_dummy_017 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

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

theorem nb093_wpp_notmem_0014 (A : Class) : (nb093_alpha_dummy_017 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_017, fv_syn_c1c] using (nb093_compact_fv_empty_0010 A)

theorem nb093_compact_fv_empty_0011 (r : Var) (d : Var) : (nb093_alpha_dummy_019 r d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0015 (r : Var) (d : Var) : (nb093_alpha_dummy_019 r d) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_019, fv_syn_c1c] using (nb093_compact_fv_empty_0011 r d)

theorem nb093_compact_fv_empty_0012 (A : Class) : (nb093_alpha_dummy_009 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0016 (A : Class) : (nb093_alpha_dummy_009 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_009, fv_syn_c1c] using (nb093_compact_fv_empty_0012 A)

theorem nb093_compact_fv_empty_0013 (r : Var) (d : Var) : (nb093_alpha_dummy_011 r d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0017 (r : Var) (d : Var) : (nb093_alpha_dummy_011 r d) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_011, fv_syn_c1c] using (nb093_compact_fv_empty_0013 r d)

theorem nb093_compact_fv_empty_0014 (A : Class) : (nb093_alpha_dummy_008 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0018 (A : Class) : (nb093_alpha_dummy_008 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_008, fv_syn_c1c] using (nb093_compact_fv_empty_0014 A)

theorem nb093_compact_fv_empty_0015 (r : Var) (d : Var) : (nb093_alpha_dummy_010 r d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0019 (r : Var) (d : Var) : (nb093_alpha_dummy_010 r d) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_010, fv_syn_c1c] using (nb093_compact_fv_empty_0015 r d)

theorem nb093_compact_fv_empty_0016 (A : Class) : (nb093_alpha_dummy_014 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0020 (A : Class) : (nb093_alpha_dummy_014 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_014, fv_syn_c1c] using (nb093_compact_fv_empty_0016 A)

theorem nb093_compact_fv_empty_0017 (r : Var) (d : Var) : (nb093_alpha_dummy_015 r d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0021 (r : Var) (d : Var) : (nb093_alpha_dummy_015 r d) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_015, fv_syn_c1c] using (nb093_compact_fv_empty_0017 r d)

theorem nb093_compact_fv_empty_0018 (A : Class) : (nb093_alpha_dummy_012 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0022 (A : Class) : (nb093_alpha_dummy_012 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_012, fv_syn_c1c] using (nb093_compact_fv_empty_0018 A)

theorem nb093_compact_fv_empty_0019 (r : Var) (d : Var) : (nb093_alpha_dummy_013 r d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0023 (r : Var) (d : Var) : (nb093_alpha_dummy_013 r d) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_013, fv_syn_c1c] using (nb093_compact_fv_empty_0019 r d)

theorem nb093_compact_fv_empty_0020 (A : Class) : (nb093_alpha_dummy_000 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0024 (A : Class) : (nb093_alpha_dummy_000 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_000, fv_syn_c1c] using (nb093_compact_fv_empty_0020 A)

theorem nb093_compact_fv_empty_0021 (d : Var) : d ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0025 (d : Var) : d ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb093_compact_fv_empty_0021 d)

theorem nb093_compact_fv_empty_0022 (A : Class) : (nb093_alpha_dummy_001 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0026 (A : Class) : (nb093_alpha_dummy_001 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_001, fv_syn_c1c] using (nb093_compact_fv_empty_0022 A)

theorem nb093_compact_fv_empty_0023 (r : Var) : r ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0027 (r : Var) : r ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb093_compact_fv_empty_0023 r)

theorem nb093_compact_fv_empty_0024 (A : Class) : (nb093_alpha_dummy_006 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0028 (A : Class) : (nb093_alpha_dummy_006 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_006, fv_syn_c1c] using (nb093_compact_fv_empty_0024 A)

theorem nb093_compact_fv_empty_0025 (r : Var) (d : Var) : (nb093_alpha_dummy_007 r d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0029 (r : Var) (d : Var) : (nb093_alpha_dummy_007 r d) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_007, fv_syn_c1c] using (nb093_compact_fv_empty_0025 r d)

theorem nb093_compact_fv_empty_0026 (A : Class) : (nb093_alpha_dummy_004 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0030 (A : Class) : (nb093_alpha_dummy_004 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_004, fv_syn_c1c] using (nb093_compact_fv_empty_0026 A)

theorem nb093_compact_fv_empty_0027 (A : Class) (r : Var) (d : Var) : (nb093_alpha_dummy_005 A r d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0031 (A : Class) (r : Var) (d : Var) : (nb093_alpha_dummy_005 A r d) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_005, fv_syn_c1c] using (nb093_compact_fv_empty_0027 A r d)

theorem nb093_compact_fv_empty_0028 (A : Class) : (nb093_alpha_dummy_002 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0032 (A : Class) : (nb093_alpha_dummy_002 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_002, fv_syn_c1c] using (nb093_compact_fv_empty_0028 A)

theorem nb093_compact_fv_empty_0029 (A : Class) (r : Var) (d : Var) : (nb093_alpha_dummy_003 A r d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0033 (A : Class) (r : Var) (d : Var) : (nb093_alpha_dummy_003 A r d) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_003, fv_syn_c1c] using (nb093_compact_fv_empty_0029 A r d)

theorem nb093_compact_envfresh_0001 (A : Class) (r : Var) (d : Var) : TEnvFresh [((nb093_alpha_dummy_024 A), (nb093_alpha_dummy_027 r d)), ((nb093_alpha_dummy_023 A), (nb093_alpha_dummy_026 r d)), ((nb093_alpha_dummy_022 A), (nb093_alpha_dummy_025 r d)), ((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_014 A), (nb093_alpha_dummy_015 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb093_alpha_dummy_024 A) (nb093_alpha_dummy_027 r d) (nb093_wpp_notmem_0004 A) (nb093_wpp_notmem_0005 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_023 A) (nb093_alpha_dummy_026 r d) (nb093_wpp_notmem_0006 A) (nb093_wpp_notmem_0007 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_022 A) (nb093_alpha_dummy_025 r d) (nb093_wpp_notmem_0008 A) (nb093_wpp_notmem_0009 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_020 A) (nb093_alpha_dummy_021 r d) (nb093_wpp_notmem_0010 A) (nb093_wpp_notmem_0011 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_016 A) (nb093_alpha_dummy_018 r d) (nb093_wpp_notmem_0012 A) (nb093_wpp_notmem_0013 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_017 A) (nb093_alpha_dummy_019 r d) (nb093_wpp_notmem_0014 A) (nb093_wpp_notmem_0015 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_009 A) (nb093_alpha_dummy_011 r d) (nb093_wpp_notmem_0016 A) (nb093_wpp_notmem_0017 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_008 A) (nb093_alpha_dummy_010 r d) (nb093_wpp_notmem_0018 A) (nb093_wpp_notmem_0019 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_014 A) (nb093_alpha_dummy_015 r d) (nb093_wpp_notmem_0020 A) (nb093_wpp_notmem_0021 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_012 A) (nb093_alpha_dummy_013 r d) (nb093_wpp_notmem_0022 A) (nb093_wpp_notmem_0023 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_000 A) d (nb093_wpp_notmem_0024 A) (nb093_wpp_notmem_0025 d) (TEnvFresh.consFresh (nb093_alpha_dummy_001 A) r (nb093_wpp_notmem_0026 A) (nb093_wpp_notmem_0027 r) (TEnvFresh.consFresh (nb093_alpha_dummy_006 A) (nb093_alpha_dummy_007 r d) (nb093_wpp_notmem_0028 A) (nb093_wpp_notmem_0029 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_004 A) (nb093_alpha_dummy_005 A r d) (nb093_wpp_notmem_0030 A) (nb093_wpp_notmem_0031 A r d) (TEnvFresh.consFresh (nb093_alpha_dummy_002 A) (nb093_alpha_dummy_003 A r d) (nb093_wpp_notmem_0032 A) (nb093_wpp_notmem_0033 A r d) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb093_wpp_refl_0001 (A : Class) (r : Var) (d : Var) : TReflOn [((nb093_alpha_dummy_024 A), (nb093_alpha_dummy_027 r d)), ((nb093_alpha_dummy_023 A), (nb093_alpha_dummy_026 r d)), ((nb093_alpha_dummy_022 A), (nb093_alpha_dummy_025 r d)), ((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_014 A), (nb093_alpha_dummy_015 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb093_compact_envfresh_0001 A r d)

theorem nb093_wpp_notmem_0034 (A : Class) : (nb093_alpha_dummy_024 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_024, fv_syn_c0] using (nb093_compact_fv_empty_0000 A)

theorem nb093_wpp_notmem_0035 (r : Var) (d : Var) : (nb093_alpha_dummy_027 r d) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_027, fv_syn_c0] using (nb093_compact_fv_empty_0001 r d)

theorem nb093_wpp_notmem_0036 (A : Class) : (nb093_alpha_dummy_023 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_023, fv_syn_c0] using (nb093_compact_fv_empty_0002 A)

theorem nb093_wpp_notmem_0037 (r : Var) (d : Var) : (nb093_alpha_dummy_026 r d) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_026, fv_syn_c0] using (nb093_compact_fv_empty_0003 r d)

theorem nb093_wpp_notmem_0038 (A : Class) : (nb093_alpha_dummy_022 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_022, fv_syn_c0] using (nb093_compact_fv_empty_0004 A)

theorem nb093_wpp_notmem_0039 (r : Var) (d : Var) : (nb093_alpha_dummy_025 r d) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_025, fv_syn_c0] using (nb093_compact_fv_empty_0005 r d)

theorem nb093_wpp_notmem_0040 (A : Class) : (nb093_alpha_dummy_020 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_020, fv_syn_c0] using (nb093_compact_fv_empty_0006 A)

theorem nb093_wpp_notmem_0041 (r : Var) (d : Var) : (nb093_alpha_dummy_021 r d) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_021, fv_syn_c0] using (nb093_compact_fv_empty_0007 r d)

theorem nb093_wpp_notmem_0042 (A : Class) : (nb093_alpha_dummy_016 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_016, fv_syn_c0] using (nb093_compact_fv_empty_0008 A)

theorem nb093_wpp_notmem_0043 (r : Var) (d : Var) : (nb093_alpha_dummy_018 r d) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_018, fv_syn_c0] using (nb093_compact_fv_empty_0009 r d)

theorem nb093_wpp_notmem_0044 (A : Class) : (nb093_alpha_dummy_017 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_017, fv_syn_c0] using (nb093_compact_fv_empty_0010 A)

theorem nb093_wpp_notmem_0045 (r : Var) (d : Var) : (nb093_alpha_dummy_019 r d) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_019, fv_syn_c0] using (nb093_compact_fv_empty_0011 r d)

theorem nb093_wpp_notmem_0046 (A : Class) : (nb093_alpha_dummy_009 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_009, fv_syn_c0] using (nb093_compact_fv_empty_0012 A)

theorem nb093_wpp_notmem_0047 (r : Var) (d : Var) : (nb093_alpha_dummy_011 r d) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_011, fv_syn_c0] using (nb093_compact_fv_empty_0013 r d)

theorem nb093_wpp_notmem_0048 (A : Class) : (nb093_alpha_dummy_008 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_008, fv_syn_c0] using (nb093_compact_fv_empty_0014 A)

theorem nb093_wpp_notmem_0049 (r : Var) (d : Var) : (nb093_alpha_dummy_010 r d) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_010, fv_syn_c0] using (nb093_compact_fv_empty_0015 r d)

theorem nb093_wpp_notmem_0050 (A : Class) : (nb093_alpha_dummy_014 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_014, fv_syn_c0] using (nb093_compact_fv_empty_0016 A)

theorem nb093_wpp_notmem_0051 (r : Var) (d : Var) : (nb093_alpha_dummy_015 r d) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_015, fv_syn_c0] using (nb093_compact_fv_empty_0017 r d)

theorem nb093_wpp_notmem_0052 (A : Class) : (nb093_alpha_dummy_012 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_012, fv_syn_c0] using (nb093_compact_fv_empty_0018 A)

theorem nb093_wpp_notmem_0053 (r : Var) (d : Var) : (nb093_alpha_dummy_013 r d) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_013, fv_syn_c0] using (nb093_compact_fv_empty_0019 r d)

theorem nb093_wpp_notmem_0054 (A : Class) : (nb093_alpha_dummy_000 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_000, fv_syn_c0] using (nb093_compact_fv_empty_0020 A)

theorem nb093_wpp_notmem_0055 (d : Var) : d ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb093_compact_fv_empty_0021 d)

theorem nb093_wpp_notmem_0056 (A : Class) : (nb093_alpha_dummy_001 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_001, fv_syn_c0] using (nb093_compact_fv_empty_0022 A)

theorem nb093_wpp_notmem_0057 (r : Var) : r ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb093_compact_fv_empty_0023 r)

theorem nb093_wpp_notmem_0058 (A : Class) : (nb093_alpha_dummy_006 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_006, fv_syn_c0] using (nb093_compact_fv_empty_0024 A)

theorem nb093_wpp_notmem_0059 (r : Var) (d : Var) : (nb093_alpha_dummy_007 r d) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_007, fv_syn_c0] using (nb093_compact_fv_empty_0025 r d)

theorem nb093_wpp_notmem_0060 (A : Class) : (nb093_alpha_dummy_004 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_004, fv_syn_c0] using (nb093_compact_fv_empty_0026 A)

theorem nb093_wpp_notmem_0061 (A : Class) (r : Var) (d : Var) : (nb093_alpha_dummy_005 A r d) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_005, fv_syn_c0] using (nb093_compact_fv_empty_0027 A r d)

theorem nb093_wpp_notmem_0062 (A : Class) : (nb093_alpha_dummy_002 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_002, fv_syn_c0] using (nb093_compact_fv_empty_0028 A)

theorem nb093_wpp_notmem_0063 (A : Class) (r : Var) (d : Var) : (nb093_alpha_dummy_003 A r d) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_003, fv_syn_c0] using (nb093_compact_fv_empty_0029 A r d)

theorem nb093_compact_envfresh_0002 (A : Class) (r : Var) (d : Var) : TEnvFresh [((nb093_alpha_dummy_024 A), (nb093_alpha_dummy_027 r d)), ((nb093_alpha_dummy_023 A), (nb093_alpha_dummy_026 r d)), ((nb093_alpha_dummy_022 A), (nb093_alpha_dummy_025 r d)), ((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_014 A), (nb093_alpha_dummy_015 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb093_alpha_dummy_024 A) (nb093_alpha_dummy_027 r d) (nb093_wpp_notmem_0034 A) (nb093_wpp_notmem_0035 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_023 A) (nb093_alpha_dummy_026 r d) (nb093_wpp_notmem_0036 A) (nb093_wpp_notmem_0037 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_022 A) (nb093_alpha_dummy_025 r d) (nb093_wpp_notmem_0038 A) (nb093_wpp_notmem_0039 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_020 A) (nb093_alpha_dummy_021 r d) (nb093_wpp_notmem_0040 A) (nb093_wpp_notmem_0041 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_016 A) (nb093_alpha_dummy_018 r d) (nb093_wpp_notmem_0042 A) (nb093_wpp_notmem_0043 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_017 A) (nb093_alpha_dummy_019 r d) (nb093_wpp_notmem_0044 A) (nb093_wpp_notmem_0045 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_009 A) (nb093_alpha_dummy_011 r d) (nb093_wpp_notmem_0046 A) (nb093_wpp_notmem_0047 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_008 A) (nb093_alpha_dummy_010 r d) (nb093_wpp_notmem_0048 A) (nb093_wpp_notmem_0049 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_014 A) (nb093_alpha_dummy_015 r d) (nb093_wpp_notmem_0050 A) (nb093_wpp_notmem_0051 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_012 A) (nb093_alpha_dummy_013 r d) (nb093_wpp_notmem_0052 A) (nb093_wpp_notmem_0053 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_000 A) d (nb093_wpp_notmem_0054 A) (nb093_wpp_notmem_0055 d) (TEnvFresh.consFresh (nb093_alpha_dummy_001 A) r (nb093_wpp_notmem_0056 A) (nb093_wpp_notmem_0057 r) (TEnvFresh.consFresh (nb093_alpha_dummy_006 A) (nb093_alpha_dummy_007 r d) (nb093_wpp_notmem_0058 A) (nb093_wpp_notmem_0059 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_004 A) (nb093_alpha_dummy_005 A r d) (nb093_wpp_notmem_0060 A) (nb093_wpp_notmem_0061 A r d) (TEnvFresh.consFresh (nb093_alpha_dummy_002 A) (nb093_alpha_dummy_003 A r d) (nb093_wpp_notmem_0062 A) (nb093_wpp_notmem_0063 A r d) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))

noncomputable def nb093_wpp_refl_0002 (A : Class) (r : Var) (d : Var) : TReflOn [((nb093_alpha_dummy_024 A), (nb093_alpha_dummy_027 r d)), ((nb093_alpha_dummy_023 A), (nb093_alpha_dummy_026 r d)), ((nb093_alpha_dummy_022 A), (nb093_alpha_dummy_025 r d)), ((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_014 A), (nb093_alpha_dummy_015 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb093_compact_envfresh_0002 A r d)

theorem nb093_wpp_notmem_0064 (A : Class) : (nb093_alpha_dummy_020 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_020, fv_syn_cnnc] using (nb093_compact_fv_empty_0006 A)

theorem nb093_wpp_notmem_0065 (r : Var) (d : Var) : (nb093_alpha_dummy_021 r d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_021, fv_syn_cnnc] using (nb093_compact_fv_empty_0007 r d)

theorem nb093_wpp_notmem_0066 (A : Class) : (nb093_alpha_dummy_016 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_016, fv_syn_cnnc] using (nb093_compact_fv_empty_0008 A)

theorem nb093_wpp_notmem_0067 (r : Var) (d : Var) : (nb093_alpha_dummy_018 r d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_018, fv_syn_cnnc] using (nb093_compact_fv_empty_0009 r d)

theorem nb093_wpp_notmem_0068 (A : Class) : (nb093_alpha_dummy_017 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_017, fv_syn_cnnc] using (nb093_compact_fv_empty_0010 A)

theorem nb093_wpp_notmem_0069 (r : Var) (d : Var) : (nb093_alpha_dummy_019 r d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_019, fv_syn_cnnc] using (nb093_compact_fv_empty_0011 r d)

theorem nb093_wpp_notmem_0070 (A : Class) : (nb093_alpha_dummy_009 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_009, fv_syn_cnnc] using (nb093_compact_fv_empty_0012 A)

theorem nb093_wpp_notmem_0071 (r : Var) (d : Var) : (nb093_alpha_dummy_011 r d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_011, fv_syn_cnnc] using (nb093_compact_fv_empty_0013 r d)

theorem nb093_wpp_notmem_0072 (A : Class) : (nb093_alpha_dummy_008 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_008, fv_syn_cnnc] using (nb093_compact_fv_empty_0014 A)

theorem nb093_wpp_notmem_0073 (r : Var) (d : Var) : (nb093_alpha_dummy_010 r d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_010, fv_syn_cnnc] using (nb093_compact_fv_empty_0015 r d)

theorem nb093_wpp_notmem_0074 (A : Class) : (nb093_alpha_dummy_014 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_014, fv_syn_cnnc] using (nb093_compact_fv_empty_0016 A)

theorem nb093_wpp_notmem_0075 (r : Var) (d : Var) : (nb093_alpha_dummy_015 r d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_015, fv_syn_cnnc] using (nb093_compact_fv_empty_0017 r d)

theorem nb093_wpp_notmem_0076 (A : Class) : (nb093_alpha_dummy_012 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_012, fv_syn_cnnc] using (nb093_compact_fv_empty_0018 A)

theorem nb093_wpp_notmem_0077 (r : Var) (d : Var) : (nb093_alpha_dummy_013 r d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_013, fv_syn_cnnc] using (nb093_compact_fv_empty_0019 r d)

theorem nb093_wpp_notmem_0078 (A : Class) : (nb093_alpha_dummy_000 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_000, fv_syn_cnnc] using (nb093_compact_fv_empty_0020 A)

theorem nb093_wpp_notmem_0079 (d : Var) : d ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb093_compact_fv_empty_0021 d)

theorem nb093_wpp_notmem_0080 (A : Class) : (nb093_alpha_dummy_001 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_001, fv_syn_cnnc] using (nb093_compact_fv_empty_0022 A)

theorem nb093_wpp_notmem_0081 (r : Var) : r ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb093_compact_fv_empty_0023 r)

theorem nb093_wpp_notmem_0082 (A : Class) : (nb093_alpha_dummy_006 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_006, fv_syn_cnnc] using (nb093_compact_fv_empty_0024 A)

theorem nb093_wpp_notmem_0083 (r : Var) (d : Var) : (nb093_alpha_dummy_007 r d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_007, fv_syn_cnnc] using (nb093_compact_fv_empty_0025 r d)

theorem nb093_wpp_notmem_0084 (A : Class) : (nb093_alpha_dummy_004 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_004, fv_syn_cnnc] using (nb093_compact_fv_empty_0026 A)

theorem nb093_wpp_notmem_0085 (A : Class) (r : Var) (d : Var) : (nb093_alpha_dummy_005 A r d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_005, fv_syn_cnnc] using (nb093_compact_fv_empty_0027 A r d)

theorem nb093_wpp_notmem_0086 (A : Class) : (nb093_alpha_dummy_002 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_002, fv_syn_cnnc] using (nb093_compact_fv_empty_0028 A)

theorem nb093_wpp_notmem_0087 (A : Class) (r : Var) (d : Var) : (nb093_alpha_dummy_003 A r d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_003, fv_syn_cnnc] using (nb093_compact_fv_empty_0029 A r d)

theorem nb093_compact_envfresh_0003 (A : Class) (r : Var) (d : Var) : TEnvFresh [((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_014 A), (nb093_alpha_dummy_015 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb093_alpha_dummy_020 A) (nb093_alpha_dummy_021 r d) (nb093_wpp_notmem_0064 A) (nb093_wpp_notmem_0065 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_016 A) (nb093_alpha_dummy_018 r d) (nb093_wpp_notmem_0066 A) (nb093_wpp_notmem_0067 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_017 A) (nb093_alpha_dummy_019 r d) (nb093_wpp_notmem_0068 A) (nb093_wpp_notmem_0069 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_009 A) (nb093_alpha_dummy_011 r d) (nb093_wpp_notmem_0070 A) (nb093_wpp_notmem_0071 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_008 A) (nb093_alpha_dummy_010 r d) (nb093_wpp_notmem_0072 A) (nb093_wpp_notmem_0073 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_014 A) (nb093_alpha_dummy_015 r d) (nb093_wpp_notmem_0074 A) (nb093_wpp_notmem_0075 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_012 A) (nb093_alpha_dummy_013 r d) (nb093_wpp_notmem_0076 A) (nb093_wpp_notmem_0077 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_000 A) d (nb093_wpp_notmem_0078 A) (nb093_wpp_notmem_0079 d) (TEnvFresh.consFresh (nb093_alpha_dummy_001 A) r (nb093_wpp_notmem_0080 A) (nb093_wpp_notmem_0081 r) (TEnvFresh.consFresh (nb093_alpha_dummy_006 A) (nb093_alpha_dummy_007 r d) (nb093_wpp_notmem_0082 A) (nb093_wpp_notmem_0083 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_004 A) (nb093_alpha_dummy_005 A r d) (nb093_wpp_notmem_0084 A) (nb093_wpp_notmem_0085 A r d) (TEnvFresh.consFresh (nb093_alpha_dummy_002 A) (nb093_alpha_dummy_003 A r d) (nb093_wpp_notmem_0086 A) (nb093_wpp_notmem_0087 A r d) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))

noncomputable def nb093_wpp_refl_0003 (A : Class) (r : Var) (d : Var) : TReflOn [((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_014 A), (nb093_alpha_dummy_015 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb093_compact_envfresh_0003 A r d)

theorem nb093_compact_fv_empty_0030 (A : Class) : (nb093_alpha_dummy_042 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0088 (A : Class) : (nb093_alpha_dummy_042 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_042, fv_syn_c1c] using (nb093_compact_fv_empty_0030 A)

theorem nb093_compact_fv_empty_0031 (r : Var) (d : Var) : (nb093_alpha_dummy_043 r d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0089 (r : Var) (d : Var) : (nb093_alpha_dummy_043 r d) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_043, fv_syn_c1c] using (nb093_compact_fv_empty_0031 r d)

theorem nb093_compact_fv_empty_0032 (A : Class) : (nb093_alpha_dummy_040 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0090 (A : Class) : (nb093_alpha_dummy_040 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_040, fv_syn_c1c] using (nb093_compact_fv_empty_0032 A)

theorem nb093_compact_fv_empty_0033 (r : Var) (d : Var) : (nb093_alpha_dummy_041 r d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0091 (r : Var) (d : Var) : (nb093_alpha_dummy_041 r d) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_041, fv_syn_c1c] using (nb093_compact_fv_empty_0033 r d)

theorem nb093_compact_fv_empty_0034 (A : Class) : (nb093_alpha_dummy_038 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0092 (A : Class) : (nb093_alpha_dummy_038 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_038, fv_syn_c1c] using (nb093_compact_fv_empty_0034 A)

theorem nb093_compact_fv_empty_0035 (r : Var) (d : Var) : (nb093_alpha_dummy_039 r d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0093 (r : Var) (d : Var) : (nb093_alpha_dummy_039 r d) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_039, fv_syn_c1c] using (nb093_compact_fv_empty_0035 r d)

theorem nb093_compact_envfresh_0004 (A : Class) (r : Var) (d : Var) : TEnvFresh [((nb093_alpha_dummy_024 A), (nb093_alpha_dummy_027 r d)), ((nb093_alpha_dummy_023 A), (nb093_alpha_dummy_026 r d)), ((nb093_alpha_dummy_022 A), (nb093_alpha_dummy_025 r d)), ((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_042 A), (nb093_alpha_dummy_043 r d)), ((nb093_alpha_dummy_040 A), (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A), (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb093_alpha_dummy_024 A) (nb093_alpha_dummy_027 r d) (nb093_wpp_notmem_0004 A) (nb093_wpp_notmem_0005 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_023 A) (nb093_alpha_dummy_026 r d) (nb093_wpp_notmem_0006 A) (nb093_wpp_notmem_0007 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_022 A) (nb093_alpha_dummy_025 r d) (nb093_wpp_notmem_0008 A) (nb093_wpp_notmem_0009 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_020 A) (nb093_alpha_dummy_021 r d) (nb093_wpp_notmem_0010 A) (nb093_wpp_notmem_0011 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_016 A) (nb093_alpha_dummy_018 r d) (nb093_wpp_notmem_0012 A) (nb093_wpp_notmem_0013 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_017 A) (nb093_alpha_dummy_019 r d) (nb093_wpp_notmem_0014 A) (nb093_wpp_notmem_0015 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_042 A) (nb093_alpha_dummy_043 r d) (nb093_wpp_notmem_0088 A) (nb093_wpp_notmem_0089 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_040 A) (nb093_alpha_dummy_041 r d) (nb093_wpp_notmem_0090 A) (nb093_wpp_notmem_0091 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_009 A) (nb093_alpha_dummy_011 r d) (nb093_wpp_notmem_0016 A) (nb093_wpp_notmem_0017 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_008 A) (nb093_alpha_dummy_010 r d) (nb093_wpp_notmem_0018 A) (nb093_wpp_notmem_0019 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_038 A) (nb093_alpha_dummy_039 r d) (nb093_wpp_notmem_0092 A) (nb093_wpp_notmem_0093 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_012 A) (nb093_alpha_dummy_013 r d) (nb093_wpp_notmem_0022 A) (nb093_wpp_notmem_0023 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_000 A) d (nb093_wpp_notmem_0024 A) (nb093_wpp_notmem_0025 d) (TEnvFresh.consFresh (nb093_alpha_dummy_001 A) r (nb093_wpp_notmem_0026 A) (nb093_wpp_notmem_0027 r) (TEnvFresh.consFresh (nb093_alpha_dummy_006 A) (nb093_alpha_dummy_007 r d) (nb093_wpp_notmem_0028 A) (nb093_wpp_notmem_0029 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_004 A) (nb093_alpha_dummy_005 A r d) (nb093_wpp_notmem_0030 A) (nb093_wpp_notmem_0031 A r d) (TEnvFresh.consFresh (nb093_alpha_dummy_002 A) (nb093_alpha_dummy_003 A r d) (nb093_wpp_notmem_0032 A) (nb093_wpp_notmem_0033 A r d) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))

noncomputable def nb093_wpp_refl_0004 (A : Class) (r : Var) (d : Var) : TReflOn [((nb093_alpha_dummy_024 A), (nb093_alpha_dummy_027 r d)), ((nb093_alpha_dummy_023 A), (nb093_alpha_dummy_026 r d)), ((nb093_alpha_dummy_022 A), (nb093_alpha_dummy_025 r d)), ((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_042 A), (nb093_alpha_dummy_043 r d)), ((nb093_alpha_dummy_040 A), (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A), (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb093_compact_envfresh_0004 A r d)

theorem nb093_wpp_notmem_0094 (A : Class) : (nb093_alpha_dummy_042 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_042, fv_syn_c0] using (nb093_compact_fv_empty_0030 A)

theorem nb093_wpp_notmem_0095 (r : Var) (d : Var) : (nb093_alpha_dummy_043 r d) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_043, fv_syn_c0] using (nb093_compact_fv_empty_0031 r d)

theorem nb093_wpp_notmem_0096 (A : Class) : (nb093_alpha_dummy_040 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_040, fv_syn_c0] using (nb093_compact_fv_empty_0032 A)

theorem nb093_wpp_notmem_0097 (r : Var) (d : Var) : (nb093_alpha_dummy_041 r d) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_041, fv_syn_c0] using (nb093_compact_fv_empty_0033 r d)

theorem nb093_wpp_notmem_0098 (A : Class) : (nb093_alpha_dummy_038 A) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_038, fv_syn_c0] using (nb093_compact_fv_empty_0034 A)

theorem nb093_wpp_notmem_0099 (r : Var) (d : Var) : (nb093_alpha_dummy_039 r d) ∉ ((syn_c0)).fv := by
  simpa only [nb093_alpha_dummy_039, fv_syn_c0] using (nb093_compact_fv_empty_0035 r d)

theorem nb093_compact_envfresh_0005 (A : Class) (r : Var) (d : Var) : TEnvFresh [((nb093_alpha_dummy_024 A), (nb093_alpha_dummy_027 r d)), ((nb093_alpha_dummy_023 A), (nb093_alpha_dummy_026 r d)), ((nb093_alpha_dummy_022 A), (nb093_alpha_dummy_025 r d)), ((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_042 A), (nb093_alpha_dummy_043 r d)), ((nb093_alpha_dummy_040 A), (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A), (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb093_alpha_dummy_024 A) (nb093_alpha_dummy_027 r d) (nb093_wpp_notmem_0034 A) (nb093_wpp_notmem_0035 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_023 A) (nb093_alpha_dummy_026 r d) (nb093_wpp_notmem_0036 A) (nb093_wpp_notmem_0037 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_022 A) (nb093_alpha_dummy_025 r d) (nb093_wpp_notmem_0038 A) (nb093_wpp_notmem_0039 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_020 A) (nb093_alpha_dummy_021 r d) (nb093_wpp_notmem_0040 A) (nb093_wpp_notmem_0041 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_016 A) (nb093_alpha_dummy_018 r d) (nb093_wpp_notmem_0042 A) (nb093_wpp_notmem_0043 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_017 A) (nb093_alpha_dummy_019 r d) (nb093_wpp_notmem_0044 A) (nb093_wpp_notmem_0045 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_042 A) (nb093_alpha_dummy_043 r d) (nb093_wpp_notmem_0094 A) (nb093_wpp_notmem_0095 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_040 A) (nb093_alpha_dummy_041 r d) (nb093_wpp_notmem_0096 A) (nb093_wpp_notmem_0097 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_009 A) (nb093_alpha_dummy_011 r d) (nb093_wpp_notmem_0046 A) (nb093_wpp_notmem_0047 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_008 A) (nb093_alpha_dummy_010 r d) (nb093_wpp_notmem_0048 A) (nb093_wpp_notmem_0049 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_038 A) (nb093_alpha_dummy_039 r d) (nb093_wpp_notmem_0098 A) (nb093_wpp_notmem_0099 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_012 A) (nb093_alpha_dummy_013 r d) (nb093_wpp_notmem_0052 A) (nb093_wpp_notmem_0053 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_000 A) d (nb093_wpp_notmem_0054 A) (nb093_wpp_notmem_0055 d) (TEnvFresh.consFresh (nb093_alpha_dummy_001 A) r (nb093_wpp_notmem_0056 A) (nb093_wpp_notmem_0057 r) (TEnvFresh.consFresh (nb093_alpha_dummy_006 A) (nb093_alpha_dummy_007 r d) (nb093_wpp_notmem_0058 A) (nb093_wpp_notmem_0059 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_004 A) (nb093_alpha_dummy_005 A r d) (nb093_wpp_notmem_0060 A) (nb093_wpp_notmem_0061 A r d) (TEnvFresh.consFresh (nb093_alpha_dummy_002 A) (nb093_alpha_dummy_003 A r d) (nb093_wpp_notmem_0062 A) (nb093_wpp_notmem_0063 A r d) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))

noncomputable def nb093_wpp_refl_0005 (A : Class) (r : Var) (d : Var) : TReflOn [((nb093_alpha_dummy_024 A), (nb093_alpha_dummy_027 r d)), ((nb093_alpha_dummy_023 A), (nb093_alpha_dummy_026 r d)), ((nb093_alpha_dummy_022 A), (nb093_alpha_dummy_025 r d)), ((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_042 A), (nb093_alpha_dummy_043 r d)), ((nb093_alpha_dummy_040 A), (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A), (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb093_compact_envfresh_0005 A r d)

theorem nb093_wpp_notmem_0100 (A : Class) : (nb093_alpha_dummy_042 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_042, fv_syn_cnnc] using (nb093_compact_fv_empty_0030 A)

theorem nb093_wpp_notmem_0101 (r : Var) (d : Var) : (nb093_alpha_dummy_043 r d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_043, fv_syn_cnnc] using (nb093_compact_fv_empty_0031 r d)

theorem nb093_wpp_notmem_0102 (A : Class) : (nb093_alpha_dummy_040 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_040, fv_syn_cnnc] using (nb093_compact_fv_empty_0032 A)

theorem nb093_wpp_notmem_0103 (r : Var) (d : Var) : (nb093_alpha_dummy_041 r d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_041, fv_syn_cnnc] using (nb093_compact_fv_empty_0033 r d)

theorem nb093_wpp_notmem_0104 (A : Class) : (nb093_alpha_dummy_038 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_038, fv_syn_cnnc] using (nb093_compact_fv_empty_0034 A)

theorem nb093_wpp_notmem_0105 (r : Var) (d : Var) : (nb093_alpha_dummy_039 r d) ∉ ((syn_cnnc)).fv := by
  simpa only [nb093_alpha_dummy_039, fv_syn_cnnc] using (nb093_compact_fv_empty_0035 r d)

theorem nb093_compact_envfresh_0006 (A : Class) (r : Var) (d : Var) : TEnvFresh [((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_042 A), (nb093_alpha_dummy_043 r d)), ((nb093_alpha_dummy_040 A), (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A), (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb093_alpha_dummy_020 A) (nb093_alpha_dummy_021 r d) (nb093_wpp_notmem_0064 A) (nb093_wpp_notmem_0065 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_016 A) (nb093_alpha_dummy_018 r d) (nb093_wpp_notmem_0066 A) (nb093_wpp_notmem_0067 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_017 A) (nb093_alpha_dummy_019 r d) (nb093_wpp_notmem_0068 A) (nb093_wpp_notmem_0069 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_042 A) (nb093_alpha_dummy_043 r d) (nb093_wpp_notmem_0100 A) (nb093_wpp_notmem_0101 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_040 A) (nb093_alpha_dummy_041 r d) (nb093_wpp_notmem_0102 A) (nb093_wpp_notmem_0103 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_009 A) (nb093_alpha_dummy_011 r d) (nb093_wpp_notmem_0070 A) (nb093_wpp_notmem_0071 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_008 A) (nb093_alpha_dummy_010 r d) (nb093_wpp_notmem_0072 A) (nb093_wpp_notmem_0073 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_038 A) (nb093_alpha_dummy_039 r d) (nb093_wpp_notmem_0104 A) (nb093_wpp_notmem_0105 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_012 A) (nb093_alpha_dummy_013 r d) (nb093_wpp_notmem_0076 A) (nb093_wpp_notmem_0077 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_000 A) d (nb093_wpp_notmem_0078 A) (nb093_wpp_notmem_0079 d) (TEnvFresh.consFresh (nb093_alpha_dummy_001 A) r (nb093_wpp_notmem_0080 A) (nb093_wpp_notmem_0081 r) (TEnvFresh.consFresh (nb093_alpha_dummy_006 A) (nb093_alpha_dummy_007 r d) (nb093_wpp_notmem_0082 A) (nb093_wpp_notmem_0083 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_004 A) (nb093_alpha_dummy_005 A r d) (nb093_wpp_notmem_0084 A) (nb093_wpp_notmem_0085 A r d) (TEnvFresh.consFresh (nb093_alpha_dummy_002 A) (nb093_alpha_dummy_003 A r d) (nb093_wpp_notmem_0086 A) (nb093_wpp_notmem_0087 A r d) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))

noncomputable def nb093_wpp_refl_0006 (A : Class) (r : Var) (d : Var) : TReflOn [((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_042 A), (nb093_alpha_dummy_043 r d)), ((nb093_alpha_dummy_040 A), (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A), (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb093_compact_envfresh_0006 A r d)

theorem nb093_wpp_notmem_0106 (A : Class) : (nb093_alpha_dummy_040 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_040, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0032 A)

theorem nb093_wpp_notmem_0107 (r : Var) (d : Var) : (nb093_alpha_dummy_041 r d) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_041, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0033 r d)

theorem nb093_wpp_notmem_0108 (A : Class) : (nb093_alpha_dummy_009 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_009, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0012 A)

theorem nb093_wpp_notmem_0109 (r : Var) (d : Var) : (nb093_alpha_dummy_011 r d) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_011, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0013 r d)

theorem nb093_wpp_notmem_0110 (A : Class) : (nb093_alpha_dummy_008 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_008, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0014 A)

theorem nb093_wpp_notmem_0111 (r : Var) (d : Var) : (nb093_alpha_dummy_010 r d) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_010, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0015 r d)

theorem nb093_wpp_notmem_0112 (A : Class) : (nb093_alpha_dummy_038 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_038, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0034 A)

theorem nb093_wpp_notmem_0113 (r : Var) (d : Var) : (nb093_alpha_dummy_039 r d) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_039, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0035 r d)

theorem nb093_wpp_notmem_0114 (A : Class) : (nb093_alpha_dummy_012 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_012, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0018 A)

theorem nb093_wpp_notmem_0115 (r : Var) (d : Var) : (nb093_alpha_dummy_013 r d) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_013, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0019 r d)

theorem nb093_wpp_notmem_0116 (A : Class) : (nb093_alpha_dummy_000 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_000, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0020 A)

theorem nb093_wpp_notmem_0117 (d : Var) : d ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0021 d)

theorem nb093_wpp_notmem_0118 (A : Class) : (nb093_alpha_dummy_001 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_001, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0022 A)

theorem nb093_wpp_notmem_0119 (r : Var) : r ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0023 r)

theorem nb093_wpp_notmem_0120 (A : Class) : (nb093_alpha_dummy_006 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_006, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0024 A)

theorem nb093_wpp_notmem_0121 (r : Var) (d : Var) : (nb093_alpha_dummy_007 r d) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_007, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0025 r d)

theorem nb093_wpp_notmem_0122 (A : Class) : (nb093_alpha_dummy_004 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_004, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0026 A)

theorem nb093_wpp_notmem_0123 (A : Class) (r : Var) (d : Var) : (nb093_alpha_dummy_005 A r d) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_005, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0027 A r d)

theorem nb093_wpp_notmem_0124 (A : Class) : (nb093_alpha_dummy_002 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_002, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0028 A)

theorem nb093_wpp_notmem_0125 (A : Class) (r : Var) (d : Var) : (nb093_alpha_dummy_003 A r d) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb093_alpha_dummy_003, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb093_compact_fv_empty_0029 A r d)

theorem nb093_compact_envfresh_0007 (A : Class) (r : Var) (d : Var) : TEnvFresh [((nb093_alpha_dummy_040 A), (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A), (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb093_alpha_dummy_040 A) (nb093_alpha_dummy_041 r d) (nb093_wpp_notmem_0106 A) (nb093_wpp_notmem_0107 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_009 A) (nb093_alpha_dummy_011 r d) (nb093_wpp_notmem_0108 A) (nb093_wpp_notmem_0109 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_008 A) (nb093_alpha_dummy_010 r d) (nb093_wpp_notmem_0110 A) (nb093_wpp_notmem_0111 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_038 A) (nb093_alpha_dummy_039 r d) (nb093_wpp_notmem_0112 A) (nb093_wpp_notmem_0113 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_012 A) (nb093_alpha_dummy_013 r d) (nb093_wpp_notmem_0114 A) (nb093_wpp_notmem_0115 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_000 A) d (nb093_wpp_notmem_0116 A) (nb093_wpp_notmem_0117 d) (TEnvFresh.consFresh (nb093_alpha_dummy_001 A) r (nb093_wpp_notmem_0118 A) (nb093_wpp_notmem_0119 r) (TEnvFresh.consFresh (nb093_alpha_dummy_006 A) (nb093_alpha_dummy_007 r d) (nb093_wpp_notmem_0120 A) (nb093_wpp_notmem_0121 r d) (TEnvFresh.consFresh (nb093_alpha_dummy_004 A) (nb093_alpha_dummy_005 A r d) (nb093_wpp_notmem_0122 A) (nb093_wpp_notmem_0123 A r d) (TEnvFresh.consFresh (nb093_alpha_dummy_002 A) (nb093_alpha_dummy_003 A r d) (nb093_wpp_notmem_0124 A) (nb093_wpp_notmem_0125 A r d) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))

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

noncomputable def nb093_wpp_refl_0007 (A : Class) (r : Var) (d : Var) : TReflOn [((nb093_alpha_dummy_040 A), (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A), (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb093_compact_envfresh_0007 A r d)

noncomputable def nb093_split_alpha_0000 (A : Class) (r : Var) (d : Var) : TAlphaWff [((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A), (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_009 A)) (Class.cv (nb093_alpha_dummy_000 A))) (Wff.neg (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_009 A))) (syn_csn (syn_c0c)))))) (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_011 r d)) (Class.cv d)) (Wff.neg (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d))) (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0032 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0034 r d) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0032 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0034 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0036 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0037 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0033 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0035 r d) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_000 A))).fv) (by decide)) (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv d)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0010 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0011 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0010 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0011 r d) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0040 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0041 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0038 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0039 r d) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_009 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_011 r d))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0014 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0015 r d) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0014 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0015 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0012 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0013 r d) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_024 A), (nb093_alpha_dummy_027 r d)), ((nb093_alpha_dummy_023 A), (nb093_alpha_dummy_026 r d)), ((nb093_alpha_dummy_022 A), (nb093_alpha_dummy_025 r d)), ((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_042 A), (nb093_alpha_dummy_043 r d)), ((nb093_alpha_dummy_040 A), (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A), (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_c1c) (nb093_wpp_refl_0004 A r d))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0018 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0019 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0016 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0017 r d) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0022 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0023 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0020 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0021 r d) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0018 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0019 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0016 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0017 r d) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0022 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0023 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0020 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0021 r d) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_024 A), (nb093_alpha_dummy_027 r d)), ((nb093_alpha_dummy_023 A), (nb093_alpha_dummy_026 r d)), ((nb093_alpha_dummy_022 A), (nb093_alpha_dummy_025 r d)), ((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_042 A), (nb093_alpha_dummy_043 r d)), ((nb093_alpha_dummy_040 A), (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A), (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_c0) (nb093_wpp_refl_0005 A r d))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0026 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0027 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0024 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0025 r d) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0026 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0027 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0024 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0025 r d) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0030 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0031 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0028 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0029 r d) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0030 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0031 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0028 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0029 r d) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0012 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0013 r d) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_042 A), (nb093_alpha_dummy_043 r d)), ((nb093_alpha_dummy_040 A), (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A), (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (nb093_wpp_refl_0006 A r d))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0012 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0013 r d) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0012 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0013 r d) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_042 A), (nb093_alpha_dummy_043 r d)), ((nb093_alpha_dummy_040 A), (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A), (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (nb093_wpp_refl_0006 A r d)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0010 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0011 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0010 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0011 r d) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0040 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0041 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0038 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0039 r d) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_009 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_011 r d))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0014 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0015 r d) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0014 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0015 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0012 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0013 r d) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_024 A), (nb093_alpha_dummy_027 r d)), ((nb093_alpha_dummy_023 A), (nb093_alpha_dummy_026 r d)), ((nb093_alpha_dummy_022 A), (nb093_alpha_dummy_025 r d)), ((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_042 A), (nb093_alpha_dummy_043 r d)), ((nb093_alpha_dummy_040 A), (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A), (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_c1c) (nb093_wpp_refl_0004 A r d))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0018 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0019 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0016 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0017 r d) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0022 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0023 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0020 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0021 r d) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0018 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0019 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0016 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0017 r d) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0022 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0023 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0020 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0021 r d) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_024 A), (nb093_alpha_dummy_027 r d)), ((nb093_alpha_dummy_023 A), (nb093_alpha_dummy_026 r d)), ((nb093_alpha_dummy_022 A), (nb093_alpha_dummy_025 r d)), ((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_042 A), (nb093_alpha_dummy_043 r d)), ((nb093_alpha_dummy_040 A), (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A), (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_c0) (nb093_wpp_refl_0005 A r d))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0026 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0027 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0024 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0025 r d) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0026 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0027 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0024 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0025 r d) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0030 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0031 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0028 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0029 r d) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0030 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0031 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0028 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0029 r d) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0012 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0013 r d) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_042 A), (nb093_alpha_dummy_043 r d)), ((nb093_alpha_dummy_040 A), (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A), (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (nb093_wpp_refl_0006 A r d))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0012 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0013 r d) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0012 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0013 r d) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_042 A), (nb093_alpha_dummy_043 r d)), ((nb093_alpha_dummy_040 A), (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A), (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (nb093_wpp_refl_0006 A r d)))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_040 A), (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A), (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_ccompl (syn_csn (syn_c0c))) (nb093_wpp_refl_0007 A r d)))))))))))

noncomputable def nb093_split_alpha_0001 (A : Class) (r : Var) (d : Var) (dv_d_r : d ≠ r) : TAlphaWff [((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_012 A)) (syn_ccompl (Class.cab (nb093_alpha_dummy_008 A) (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A)) (syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))))))) (Wff.neg (Wff.classMem (Class.cv (nb093_alpha_dummy_012 A)) (syn_ccompl (Class.cab (nb093_alpha_dummy_008 A) (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_000 A)) (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_009 A))) (syn_csn (syn_c0c)))))))))) (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_013 r d)) (syn_ccompl (Class.cab (nb093_alpha_dummy_010 r d) (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv r) (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d)) (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))))))) (Wff.neg (Wff.classMem (Class.cv (nb093_alpha_dummy_013 r d)) (syn_ccompl (Class.cab (nb093_alpha_dummy_010 r d) (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv d) (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d)) (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d))) (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0004 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0006 r d) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0004 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0006 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0008 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0009 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0005 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0007 r d) 0)) (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) (Ne.symm dv_d_r) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_000 A))).fv) (by decide)) (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv d)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0010 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0011 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0010 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0011 r d) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_009 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_011 r d))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0014 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0015 r d) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0014 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0015 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0012 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0013 r d) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_024 A), (nb093_alpha_dummy_027 r d)), ((nb093_alpha_dummy_023 A), (nb093_alpha_dummy_026 r d)), ((nb093_alpha_dummy_022 A), (nb093_alpha_dummy_025 r d)), ((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_014 A), (nb093_alpha_dummy_015 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_c1c) (nb093_wpp_refl_0001 A r d))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0018 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0019 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0016 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0017 r d) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0022 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0023 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0020 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0021 r d) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0018 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0019 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0016 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0017 r d) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0022 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0023 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0020 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0021 r d) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_024 A), (nb093_alpha_dummy_027 r d)), ((nb093_alpha_dummy_023 A), (nb093_alpha_dummy_026 r d)), ((nb093_alpha_dummy_022 A), (nb093_alpha_dummy_025 r d)), ((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_014 A), (nb093_alpha_dummy_015 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_c0) (nb093_wpp_refl_0002 A r d))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0026 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0027 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0024 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0025 r d) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0026 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0027 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0024 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0025 r d) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0030 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0031 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0028 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0029 r d) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0030 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0031 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0028 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0029 r d) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0012 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0013 r d) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_014 A), (nb093_alpha_dummy_015 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (nb093_wpp_refl_0003 A r d))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0012 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0013 r d) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0012 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0013 r d) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_014 A), (nb093_alpha_dummy_015 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (nb093_wpp_refl_0003 A r d)))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0004 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0006 r d) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0004 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0006 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0008 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0009 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0005 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0007 r d) 0)) (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) (Ne.symm dv_d_r) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_000 A))).fv) (by decide)) (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv d)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0010 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0011 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0010 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0011 r d) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_009 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_011 r d))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0014 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0015 r d) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0014 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0015 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0012 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0013 r d) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_024 A), (nb093_alpha_dummy_027 r d)), ((nb093_alpha_dummy_023 A), (nb093_alpha_dummy_026 r d)), ((nb093_alpha_dummy_022 A), (nb093_alpha_dummy_025 r d)), ((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_014 A), (nb093_alpha_dummy_015 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_c1c) (nb093_wpp_refl_0001 A r d))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0018 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0019 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0016 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0017 r d) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0022 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0023 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0020 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0021 r d) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0018 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0019 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0016 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0017 r d) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0022 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0023 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0020 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0021 r d) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_024 A), (nb093_alpha_dummy_027 r d)), ((nb093_alpha_dummy_023 A), (nb093_alpha_dummy_026 r d)), ((nb093_alpha_dummy_022 A), (nb093_alpha_dummy_025 r d)), ((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_014 A), (nb093_alpha_dummy_015 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_c0) (nb093_wpp_refl_0002 A r d))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0026 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0027 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0024 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0025 r d) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0026 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0027 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0024 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0025 r d) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0030 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0031 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0028 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0029 r d) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0030 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0031 r d) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0028 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0029 r d) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0012 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0013 r d) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_014 A), (nb093_alpha_dummy_015 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (nb093_wpp_refl_0003 A r d))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0012 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0013 r d) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0012 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0013 r d) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_014 A), (nb093_alpha_dummy_015 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (nb093_wpp_refl_0003 A r d)))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb093_split_alpha_0000 A r d))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb093_split_alpha_0000 A r d)))))))))))))))

theorem nb093_compact_fv_empty_0036 (A : Class) : (nb093_alpha_dummy_080 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0126 (A : Class) : (nb093_alpha_dummy_080 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_080, fv_syn_c1c] using (nb093_compact_fv_empty_0036 A)

theorem nb093_compact_fv_empty_0037 (r : Var) : (nb093_alpha_dummy_083 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0127 (r : Var) : (nb093_alpha_dummy_083 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_083, fv_syn_c1c] using (nb093_compact_fv_empty_0037 r)

theorem nb093_compact_fv_empty_0038 (A : Class) : (nb093_alpha_dummy_079 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0128 (A : Class) : (nb093_alpha_dummy_079 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_079, fv_syn_c1c] using (nb093_compact_fv_empty_0038 A)

theorem nb093_compact_fv_empty_0039 (r : Var) : (nb093_alpha_dummy_082 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0129 (r : Var) : (nb093_alpha_dummy_082 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_082, fv_syn_c1c] using (nb093_compact_fv_empty_0039 r)

theorem nb093_compact_fv_empty_0040 (A : Class) : (nb093_alpha_dummy_078 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0130 (A : Class) : (nb093_alpha_dummy_078 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_078, fv_syn_c1c] using (nb093_compact_fv_empty_0040 A)

theorem nb093_compact_fv_empty_0041 (r : Var) : (nb093_alpha_dummy_081 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0131 (r : Var) : (nb093_alpha_dummy_081 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_081, fv_syn_c1c] using (nb093_compact_fv_empty_0041 r)

theorem nb093_compact_fv_empty_0042 (A : Class) : (nb093_alpha_dummy_076 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0132 (A : Class) : (nb093_alpha_dummy_076 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_076, fv_syn_c1c] using (nb093_compact_fv_empty_0042 A)

theorem nb093_compact_fv_empty_0043 (r : Var) : (nb093_alpha_dummy_077 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0133 (r : Var) : (nb093_alpha_dummy_077 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_077, fv_syn_c1c] using (nb093_compact_fv_empty_0043 r)

theorem nb093_compact_fv_empty_0044 (A : Class) : (nb093_alpha_dummy_072 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0134 (A : Class) : (nb093_alpha_dummy_072 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_072, fv_syn_c1c] using (nb093_compact_fv_empty_0044 A)

theorem nb093_compact_fv_empty_0045 (r : Var) : (nb093_alpha_dummy_074 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0135 (r : Var) : (nb093_alpha_dummy_074 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_074, fv_syn_c1c] using (nb093_compact_fv_empty_0045 r)

theorem nb093_compact_fv_empty_0046 (A : Class) : (nb093_alpha_dummy_073 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0136 (A : Class) : (nb093_alpha_dummy_073 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_073, fv_syn_c1c] using (nb093_compact_fv_empty_0046 A)

theorem nb093_compact_fv_empty_0047 (r : Var) : (nb093_alpha_dummy_075 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0137 (r : Var) : (nb093_alpha_dummy_075 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_075, fv_syn_c1c] using (nb093_compact_fv_empty_0047 r)

theorem nb093_compact_fv_empty_0048 (A : Class) : (nb093_alpha_dummy_065 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0138 (A : Class) : (nb093_alpha_dummy_065 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_065, fv_syn_c1c] using (nb093_compact_fv_empty_0048 A)

theorem nb093_compact_fv_empty_0049 (r : Var) : (nb093_alpha_dummy_067 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0139 (r : Var) : (nb093_alpha_dummy_067 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_067, fv_syn_c1c] using (nb093_compact_fv_empty_0049 r)

theorem nb093_compact_fv_empty_0050 (A : Class) : (nb093_alpha_dummy_064 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0140 (A : Class) : (nb093_alpha_dummy_064 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_064, fv_syn_c1c] using (nb093_compact_fv_empty_0050 A)

theorem nb093_compact_fv_empty_0051 (r : Var) : (nb093_alpha_dummy_066 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0141 (r : Var) : (nb093_alpha_dummy_066 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_066, fv_syn_c1c] using (nb093_compact_fv_empty_0051 r)

theorem nb093_compact_fv_empty_0052 (A : Class) : (nb093_alpha_dummy_070 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0142 (A : Class) : (nb093_alpha_dummy_070 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_070, fv_syn_c1c] using (nb093_compact_fv_empty_0052 A)

theorem nb093_compact_fv_empty_0053 (r : Var) : (nb093_alpha_dummy_071 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0143 (r : Var) : (nb093_alpha_dummy_071 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_071, fv_syn_c1c] using (nb093_compact_fv_empty_0053 r)

theorem nb093_compact_fv_empty_0054 (A : Class) : (nb093_alpha_dummy_068 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0144 (A : Class) : (nb093_alpha_dummy_068 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_068, fv_syn_c1c] using (nb093_compact_fv_empty_0054 A)

theorem nb093_compact_fv_empty_0055 (r : Var) : (nb093_alpha_dummy_069 r) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0145 (r : Var) : (nb093_alpha_dummy_069 r) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_069, fv_syn_c1c] using (nb093_compact_fv_empty_0055 r)

theorem nb093_compact_fv_empty_0056 (A : Class) : (nb093_alpha_dummy_059 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb093_wpp_notmem_0146 (A : Class) : (nb093_alpha_dummy_059 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb093_alpha_dummy_059, fv_syn_c1c] using (nb093_compact_fv_empty_0056 A)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
