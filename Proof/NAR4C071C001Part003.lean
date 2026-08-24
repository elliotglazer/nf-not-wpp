import NAR4C071C001Part002

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

theorem nb071_support_mem_0054 : (nb071_alpha_dummy_065) ∈ (((Class.cv (nb071_alpha_dummy_065))).fv ∪ ((Class.cv (nb071_alpha_dummy_042))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0055 (x : Var) : (nb071_alpha_dummy_066 x) ∈ (((Class.cv (nb071_alpha_dummy_066 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_044 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0056 : (nb071_alpha_dummy_042) ∈ (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb071_alpha_dummy_042))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_csn]
  rw [fv_syn_cpw1]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0057 (x : Var) : (nb071_alpha_dummy_044 x) ∈ (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_csn]
  rw [fv_syn_cpw1]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0058 : (nb071_alpha_dummy_042) ∈ (((syn_cpw1 (Class.cv (nb071_alpha_dummy_042)))).fv) := by
  rw [fv_syn_cpw1]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0059 (x : Var) : (nb071_alpha_dummy_044 x) ∈ (((syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x)))).fv) := by
  rw [fv_syn_cpw1]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0060 : (nb071_alpha_dummy_042) ∈ (((syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_042))) (syn_c1c))).fv ∪ ((syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_042))) (syn_c1c))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_cpw]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0061 (x : Var) : (nb071_alpha_dummy_044 x) ∈ (((syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_044 x))) (syn_c1c))).fv ∪ ((syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_044 x))) (syn_c1c))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_cpw]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0062 : (nb071_alpha_dummy_042) ∈ (((syn_cpw (Class.cv (nb071_alpha_dummy_042)))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cpw]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0063 (x : Var) : (nb071_alpha_dummy_044 x) ∈ (((syn_cpw (Class.cv (nb071_alpha_dummy_044 x)))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cpw]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0064 : (nb071_alpha_dummy_042) ∈ (((Class.cv (nb071_alpha_dummy_042))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0065 (x : Var) : (nb071_alpha_dummy_044 x) ∈ (((Class.cv (nb071_alpha_dummy_044 x))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0066 : (nb071_alpha_dummy_042) ∈ (((syn_cnin (Class.cv (nb071_alpha_dummy_065)) (Class.cv (nb071_alpha_dummy_042)))).fv ∪ ((syn_cnin (Class.cv (nb071_alpha_dummy_065)) (Class.cv (nb071_alpha_dummy_042)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0067 (x : Var) : (nb071_alpha_dummy_044 x) ∈ (((syn_cnin (Class.cv (nb071_alpha_dummy_066 x)) (Class.cv (nb071_alpha_dummy_044 x)))).fv ∪ ((syn_cnin (Class.cv (nb071_alpha_dummy_066 x)) (Class.cv (nb071_alpha_dummy_044 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0068 : (nb071_alpha_dummy_042) ∈ (((Class.cv (nb071_alpha_dummy_065))).fv ∪ ((Class.cv (nb071_alpha_dummy_042))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0069 (x : Var) : (nb071_alpha_dummy_044 x) ∈ (((Class.cv (nb071_alpha_dummy_066 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_044 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0070 : (nb071_alpha_dummy_056) ∈ (((Class.cv (nb071_alpha_dummy_056))).fv ∪ ((Class.cv (nb071_alpha_dummy_055))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0071 : (nb071_alpha_dummy_056) ∈ (((syn_ccompl (Class.cab (nb071_alpha_dummy_071) (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_056)) (Wff.classEq (Class.cv (nb071_alpha_dummy_071)) (syn_cphi (Class.cv (nb071_alpha_dummy_072)))))))).fv ∪ ((syn_ccompl (Class.cab (nb071_alpha_dummy_071) (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055)) (Wff.classEq (Class.cv (nb071_alpha_dummy_071)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0070) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0070) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0072 (x : Var) : (nb071_alpha_dummy_058 x) ∈ (((Class.cv (nb071_alpha_dummy_058 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_057 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0073 (x : Var) : (nb071_alpha_dummy_058 x) ∈ (((syn_ccompl (Class.cab (nb071_alpha_dummy_073 x) (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_058 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x)) (syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb071_alpha_dummy_073 x) (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0072 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0072 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0074 : (nb071_alpha_dummy_056) ∈ (((Class.cab (nb071_alpha_dummy_071) (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_056)) (Wff.classEq (Class.cv (nb071_alpha_dummy_071)) (syn_cphi (Class.cv (nb071_alpha_dummy_072))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_071) (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_056)) (Wff.classEq (Class.cv (nb071_alpha_dummy_071)) (syn_cphi (Class.cv (nb071_alpha_dummy_072))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0070) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0070) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0075 (x : Var) : (nb071_alpha_dummy_058 x) ∈ (((Class.cab (nb071_alpha_dummy_073 x) (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_058 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x)) (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_073 x) (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_058 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x)) (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0072 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0072 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0076 : (nb071_alpha_dummy_072) ∈ (((Class.cv (nb071_alpha_dummy_072))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0077 (x : Var) : (nb071_alpha_dummy_074 x) ∈ (((Class.cv (nb071_alpha_dummy_074 x))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0078 : (nb071_alpha_dummy_079) ∈ (((Wff.classMem (Class.cv (nb071_alpha_dummy_079)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb071_alpha_dummy_079)) (syn_c1c))).fv ∪ ((Class.cv (nb071_alpha_dummy_079))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0079 (x : Var) : (nb071_alpha_dummy_081 x) ∈ (((Wff.classMem (Class.cv (nb071_alpha_dummy_081 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb071_alpha_dummy_081 x)) (syn_c1c))).fv ∪ ((Class.cv (nb071_alpha_dummy_081 x))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0080 : (nb071_alpha_dummy_079) ∈ (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0081 (x : Var) : (nb071_alpha_dummy_081 x) ∈ (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0082 : (nb071_alpha_dummy_086) ∈ (((syn_cnin (Class.cv (nb071_alpha_dummy_086)) (Class.cv (nb071_alpha_dummy_087)))).fv ∪ ((syn_cnin (Class.cv (nb071_alpha_dummy_086)) (Class.cv (nb071_alpha_dummy_087)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0083 (x : Var) : (nb071_alpha_dummy_089 x) ∈ (((syn_cnin (Class.cv (nb071_alpha_dummy_089 x)) (Class.cv (nb071_alpha_dummy_090 x)))).fv ∪ ((syn_cnin (Class.cv (nb071_alpha_dummy_089 x)) (Class.cv (nb071_alpha_dummy_090 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0084 : (nb071_alpha_dummy_086) ∈ (((Class.cv (nb071_alpha_dummy_086))).fv ∪ ((Class.cv (nb071_alpha_dummy_087))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0085 (x : Var) : (nb071_alpha_dummy_089 x) ∈ (((Class.cv (nb071_alpha_dummy_089 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_090 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0086 : (nb071_alpha_dummy_087) ∈ (((syn_cnin (Class.cv (nb071_alpha_dummy_086)) (Class.cv (nb071_alpha_dummy_087)))).fv ∪ ((syn_cnin (Class.cv (nb071_alpha_dummy_086)) (Class.cv (nb071_alpha_dummy_087)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0087 (x : Var) : (nb071_alpha_dummy_090 x) ∈ (((syn_cnin (Class.cv (nb071_alpha_dummy_089 x)) (Class.cv (nb071_alpha_dummy_090 x)))).fv ∪ ((syn_cnin (Class.cv (nb071_alpha_dummy_089 x)) (Class.cv (nb071_alpha_dummy_090 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0088 : (nb071_alpha_dummy_087) ∈ (((Class.cv (nb071_alpha_dummy_086))).fv ∪ ((Class.cv (nb071_alpha_dummy_087))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0089 (x : Var) : (nb071_alpha_dummy_090 x) ∈ (((Class.cv (nb071_alpha_dummy_089 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_090 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0090 : (nb071_alpha_dummy_086) ∈ (((syn_ccompl (Class.cv (nb071_alpha_dummy_086)))).fv ∪ ((syn_ccompl (Class.cv (nb071_alpha_dummy_087)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0091 (x : Var) : (nb071_alpha_dummy_089 x) ∈ (((syn_ccompl (Class.cv (nb071_alpha_dummy_089 x)))).fv ∪ ((syn_ccompl (Class.cv (nb071_alpha_dummy_090 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0092 : (nb071_alpha_dummy_086) ∈ (((Class.cv (nb071_alpha_dummy_086))).fv ∪ ((Class.cv (nb071_alpha_dummy_086))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0093 (x : Var) : (nb071_alpha_dummy_089 x) ∈ (((Class.cv (nb071_alpha_dummy_089 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_089 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0094 : (nb071_alpha_dummy_087) ∈ (((syn_ccompl (Class.cv (nb071_alpha_dummy_086)))).fv ∪ ((syn_ccompl (Class.cv (nb071_alpha_dummy_087)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0095 (x : Var) : (nb071_alpha_dummy_090 x) ∈ (((syn_ccompl (Class.cv (nb071_alpha_dummy_089 x)))).fv ∪ ((syn_ccompl (Class.cv (nb071_alpha_dummy_090 x)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0096 : (nb071_alpha_dummy_087) ∈ (((Class.cv (nb071_alpha_dummy_087))).fv ∪ ((Class.cv (nb071_alpha_dummy_087))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0097 (x : Var) : (nb071_alpha_dummy_090 x) ∈ (((Class.cv (nb071_alpha_dummy_090 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_090 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0098 : (nb071_alpha_dummy_055) ∈ (((Class.cv (nb071_alpha_dummy_056))).fv ∪ ((Class.cv (nb071_alpha_dummy_055))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0099 : (nb071_alpha_dummy_055) ∈ (((syn_ccompl (Class.cab (nb071_alpha_dummy_071) (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_056)) (Wff.classEq (Class.cv (nb071_alpha_dummy_071)) (syn_cphi (Class.cv (nb071_alpha_dummy_072)))))))).fv ∪ ((syn_ccompl (Class.cab (nb071_alpha_dummy_071) (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055)) (Wff.classEq (Class.cv (nb071_alpha_dummy_071)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0098) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0098) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0100 (x : Var) : (nb071_alpha_dummy_057 x) ∈ (((Class.cv (nb071_alpha_dummy_058 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_057 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0101 (x : Var) : (nb071_alpha_dummy_057 x) ∈ (((syn_ccompl (Class.cab (nb071_alpha_dummy_073 x) (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_058 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x)) (syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb071_alpha_dummy_073 x) (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0100 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0100 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0102 : (nb071_alpha_dummy_055) ∈ (((Class.cab (nb071_alpha_dummy_071) (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055)) (Wff.classEq (Class.cv (nb071_alpha_dummy_071)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_071) (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055)) (Wff.classEq (Class.cv (nb071_alpha_dummy_071)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0098) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0098) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0103 (x : Var) : (nb071_alpha_dummy_057 x) ∈ (((Class.cab (nb071_alpha_dummy_073 x) (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_073 x) (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x)) (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x)) (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0100 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0100 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0104 : (nb071_alpha_dummy_072) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb071_alpha_dummy_072))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0105 (x : Var) : (nb071_alpha_dummy_074 x) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0106 : (nb071_alpha_dummy_072) ∈ (((syn_cphi (Class.cv (nb071_alpha_dummy_072)))).fv ∪ ((syn_cphi (Class.cv (nb071_alpha_dummy_072)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0107 (x : Var) : (nb071_alpha_dummy_074 x) ∈ (((syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))).fv ∪ ((syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0108 : (nb071_alpha_dummy_045) ∈ (((Class.cv (nb071_alpha_dummy_045))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0109 (x : Var) : (nb071_alpha_dummy_046 x) ∈ (((Class.cv (nb071_alpha_dummy_046 x))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_compact_fv_empty_0000 : (nb071_alpha_dummy_021) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0000 : (nb071_alpha_dummy_021) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_021, fv_syn_c1c] using (nb071_compact_fv_empty_0000)

theorem nb071_compact_fv_empty_0001 (x : Var) : (nb071_alpha_dummy_024 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0001 (x : Var) : (nb071_alpha_dummy_024 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_024, fv_syn_c1c] using (nb071_compact_fv_empty_0001 x)

theorem nb071_compact_fv_empty_0002 : (nb071_alpha_dummy_020) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0002 : (nb071_alpha_dummy_020) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_020, fv_syn_c1c] using (nb071_compact_fv_empty_0002)

theorem nb071_compact_fv_empty_0003 (x : Var) : (nb071_alpha_dummy_023 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0003 (x : Var) : (nb071_alpha_dummy_023 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_023, fv_syn_c1c] using (nb071_compact_fv_empty_0003 x)

theorem nb071_compact_fv_empty_0004 : (nb071_alpha_dummy_019) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0004 : (nb071_alpha_dummy_019) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_019, fv_syn_c1c] using (nb071_compact_fv_empty_0004)

theorem nb071_compact_fv_empty_0005 (x : Var) : (nb071_alpha_dummy_022 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0005 (x : Var) : (nb071_alpha_dummy_022 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_022, fv_syn_c1c] using (nb071_compact_fv_empty_0005 x)

theorem nb071_compact_fv_empty_0006 : (nb071_alpha_dummy_017) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0006 : (nb071_alpha_dummy_017) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_017, fv_syn_c1c] using (nb071_compact_fv_empty_0006)

theorem nb071_compact_fv_empty_0007 (x : Var) : (nb071_alpha_dummy_018 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0007 (x : Var) : (nb071_alpha_dummy_018 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_018, fv_syn_c1c] using (nb071_compact_fv_empty_0007 x)

theorem nb071_compact_fv_empty_0008 : (nb071_alpha_dummy_013) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0008 : (nb071_alpha_dummy_013) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_013, fv_syn_c1c] using (nb071_compact_fv_empty_0008)

theorem nb071_compact_fv_empty_0009 (x : Var) : (nb071_alpha_dummy_015 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0009 (x : Var) : (nb071_alpha_dummy_015 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_015, fv_syn_c1c] using (nb071_compact_fv_empty_0009 x)

theorem nb071_compact_fv_empty_0010 : (nb071_alpha_dummy_014) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0010 : (nb071_alpha_dummy_014) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_014, fv_syn_c1c] using (nb071_compact_fv_empty_0010)

theorem nb071_compact_fv_empty_0011 (x : Var) : (nb071_alpha_dummy_016 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0011 (x : Var) : (nb071_alpha_dummy_016 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_016, fv_syn_c1c] using (nb071_compact_fv_empty_0011 x)

theorem nb071_compact_fv_empty_0012 : (nb071_alpha_dummy_006) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0012 : (nb071_alpha_dummy_006) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_006, fv_syn_c1c] using (nb071_compact_fv_empty_0012)

theorem nb071_compact_fv_empty_0013 (x : Var) : (nb071_alpha_dummy_008 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0013 (x : Var) : (nb071_alpha_dummy_008 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_008, fv_syn_c1c] using (nb071_compact_fv_empty_0013 x)

theorem nb071_compact_fv_empty_0014 : (nb071_alpha_dummy_005) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0014 : (nb071_alpha_dummy_005) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_005, fv_syn_c1c] using (nb071_compact_fv_empty_0014)

theorem nb071_compact_fv_empty_0015 (x : Var) : (nb071_alpha_dummy_007 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0015 (x : Var) : (nb071_alpha_dummy_007 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_007, fv_syn_c1c] using (nb071_compact_fv_empty_0015 x)

theorem nb071_compact_fv_empty_0016 : (nb071_alpha_dummy_011) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0016 : (nb071_alpha_dummy_011) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_011, fv_syn_c1c] using (nb071_compact_fv_empty_0016)

theorem nb071_compact_fv_empty_0017 (x : Var) : (nb071_alpha_dummy_012 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0017 (x : Var) : (nb071_alpha_dummy_012 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_012, fv_syn_c1c] using (nb071_compact_fv_empty_0017 x)

theorem nb071_compact_fv_empty_0018 : (nb071_alpha_dummy_009) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0018 : (nb071_alpha_dummy_009) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_009, fv_syn_c1c] using (nb071_compact_fv_empty_0018)

theorem nb071_compact_fv_empty_0019 (x : Var) : (nb071_alpha_dummy_010 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0019 (x : Var) : (nb071_alpha_dummy_010 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_010, fv_syn_c1c] using (nb071_compact_fv_empty_0019 x)

theorem nb071_compact_fv_empty_0020 : (nb071_alpha_dummy_001) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0020 : (nb071_alpha_dummy_001) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_001, fv_syn_c1c] using (nb071_compact_fv_empty_0020)

theorem nb071_compact_fv_empty_0021 (x : Var) : (nb071_alpha_dummy_002 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0021 (x : Var) : (nb071_alpha_dummy_002 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_002, fv_syn_c1c] using (nb071_compact_fv_empty_0021 x)

theorem nb071_compact_fv_empty_0022 : (nb071_alpha_dummy_000) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0022 : (nb071_alpha_dummy_000) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_000, fv_syn_c1c] using (nb071_compact_fv_empty_0022)

theorem nb071_compact_fv_empty_0023 (x : Var) : x ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0023 (x : Var) : x ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb071_compact_fv_empty_0023 x)

theorem nb071_compact_fv_empty_0024 : (nb071_alpha_dummy_003) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0024 : (nb071_alpha_dummy_003) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_003, fv_syn_c1c] using (nb071_compact_fv_empty_0024)

theorem nb071_compact_fv_empty_0025 (x : Var) : (nb071_alpha_dummy_004 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0025 (x : Var) : (nb071_alpha_dummy_004 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_004, fv_syn_c1c] using (nb071_compact_fv_empty_0025 x)

theorem nb071_compact_envfresh_0000 (x : Var) : TEnvFresh [((nb071_alpha_dummy_021), (nb071_alpha_dummy_024 x)), ((nb071_alpha_dummy_020), (nb071_alpha_dummy_023 x)), ((nb071_alpha_dummy_019), (nb071_alpha_dummy_022 x)), ((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)), ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)), ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_011), (nb071_alpha_dummy_012 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb071_alpha_dummy_021) (nb071_alpha_dummy_024 x) (nb071_wpp_notmem_0000) (nb071_wpp_notmem_0001 x) (TEnvFresh.consFresh (nb071_alpha_dummy_020) (nb071_alpha_dummy_023 x) (nb071_wpp_notmem_0002) (nb071_wpp_notmem_0003 x) (TEnvFresh.consFresh (nb071_alpha_dummy_019) (nb071_alpha_dummy_022 x) (nb071_wpp_notmem_0004) (nb071_wpp_notmem_0005 x) (TEnvFresh.consFresh (nb071_alpha_dummy_017) (nb071_alpha_dummy_018 x) (nb071_wpp_notmem_0006) (nb071_wpp_notmem_0007 x) (TEnvFresh.consFresh (nb071_alpha_dummy_013) (nb071_alpha_dummy_015 x) (nb071_wpp_notmem_0008) (nb071_wpp_notmem_0009 x) (TEnvFresh.consFresh (nb071_alpha_dummy_014) (nb071_alpha_dummy_016 x) (nb071_wpp_notmem_0010) (nb071_wpp_notmem_0011 x) (TEnvFresh.consFresh (nb071_alpha_dummy_006) (nb071_alpha_dummy_008 x) (nb071_wpp_notmem_0012) (nb071_wpp_notmem_0013 x) (TEnvFresh.consFresh (nb071_alpha_dummy_005) (nb071_alpha_dummy_007 x) (nb071_wpp_notmem_0014) (nb071_wpp_notmem_0015 x) (TEnvFresh.consFresh (nb071_alpha_dummy_011) (nb071_alpha_dummy_012 x) (nb071_wpp_notmem_0016) (nb071_wpp_notmem_0017 x) (TEnvFresh.consFresh (nb071_alpha_dummy_009) (nb071_alpha_dummy_010 x) (nb071_wpp_notmem_0018) (nb071_wpp_notmem_0019 x) (TEnvFresh.consFresh (nb071_alpha_dummy_001) (nb071_alpha_dummy_002 x) (nb071_wpp_notmem_0020) (nb071_wpp_notmem_0021 x) (TEnvFresh.consFresh (nb071_alpha_dummy_000) x (nb071_wpp_notmem_0022) (nb071_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb071_alpha_dummy_003) (nb071_alpha_dummy_004 x) (nb071_wpp_notmem_0024) (nb071_wpp_notmem_0025 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))

noncomputable def nb071_wpp_refl_0000 (x : Var) : TReflOn [((nb071_alpha_dummy_021), (nb071_alpha_dummy_024 x)), ((nb071_alpha_dummy_020), (nb071_alpha_dummy_023 x)), ((nb071_alpha_dummy_019), (nb071_alpha_dummy_022 x)), ((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)), ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)), ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_011), (nb071_alpha_dummy_012 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb071_compact_envfresh_0000 x)

theorem nb071_wpp_notmem_0026 : (nb071_alpha_dummy_021) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_021, fv_syn_c0] using (nb071_compact_fv_empty_0000)

theorem nb071_wpp_notmem_0027 (x : Var) : (nb071_alpha_dummy_024 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_024, fv_syn_c0] using (nb071_compact_fv_empty_0001 x)

theorem nb071_wpp_notmem_0028 : (nb071_alpha_dummy_020) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_020, fv_syn_c0] using (nb071_compact_fv_empty_0002)

theorem nb071_wpp_notmem_0029 (x : Var) : (nb071_alpha_dummy_023 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_023, fv_syn_c0] using (nb071_compact_fv_empty_0003 x)

theorem nb071_wpp_notmem_0030 : (nb071_alpha_dummy_019) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_019, fv_syn_c0] using (nb071_compact_fv_empty_0004)

theorem nb071_wpp_notmem_0031 (x : Var) : (nb071_alpha_dummy_022 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_022, fv_syn_c0] using (nb071_compact_fv_empty_0005 x)

theorem nb071_wpp_notmem_0032 : (nb071_alpha_dummy_017) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_017, fv_syn_c0] using (nb071_compact_fv_empty_0006)

theorem nb071_wpp_notmem_0033 (x : Var) : (nb071_alpha_dummy_018 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_018, fv_syn_c0] using (nb071_compact_fv_empty_0007 x)

theorem nb071_wpp_notmem_0034 : (nb071_alpha_dummy_013) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_013, fv_syn_c0] using (nb071_compact_fv_empty_0008)

theorem nb071_wpp_notmem_0035 (x : Var) : (nb071_alpha_dummy_015 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_015, fv_syn_c0] using (nb071_compact_fv_empty_0009 x)

theorem nb071_wpp_notmem_0036 : (nb071_alpha_dummy_014) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_014, fv_syn_c0] using (nb071_compact_fv_empty_0010)

theorem nb071_wpp_notmem_0037 (x : Var) : (nb071_alpha_dummy_016 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_016, fv_syn_c0] using (nb071_compact_fv_empty_0011 x)

theorem nb071_wpp_notmem_0038 : (nb071_alpha_dummy_006) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_006, fv_syn_c0] using (nb071_compact_fv_empty_0012)

theorem nb071_wpp_notmem_0039 (x : Var) : (nb071_alpha_dummy_008 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_008, fv_syn_c0] using (nb071_compact_fv_empty_0013 x)

theorem nb071_wpp_notmem_0040 : (nb071_alpha_dummy_005) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_005, fv_syn_c0] using (nb071_compact_fv_empty_0014)

theorem nb071_wpp_notmem_0041 (x : Var) : (nb071_alpha_dummy_007 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_007, fv_syn_c0] using (nb071_compact_fv_empty_0015 x)

theorem nb071_wpp_notmem_0042 : (nb071_alpha_dummy_011) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_011, fv_syn_c0] using (nb071_compact_fv_empty_0016)

theorem nb071_wpp_notmem_0043 (x : Var) : (nb071_alpha_dummy_012 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_012, fv_syn_c0] using (nb071_compact_fv_empty_0017 x)

theorem nb071_wpp_notmem_0044 : (nb071_alpha_dummy_009) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_009, fv_syn_c0] using (nb071_compact_fv_empty_0018)

theorem nb071_wpp_notmem_0045 (x : Var) : (nb071_alpha_dummy_010 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_010, fv_syn_c0] using (nb071_compact_fv_empty_0019 x)

theorem nb071_wpp_notmem_0046 : (nb071_alpha_dummy_001) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_001, fv_syn_c0] using (nb071_compact_fv_empty_0020)

theorem nb071_wpp_notmem_0047 (x : Var) : (nb071_alpha_dummy_002 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_002, fv_syn_c0] using (nb071_compact_fv_empty_0021 x)

theorem nb071_wpp_notmem_0048 : (nb071_alpha_dummy_000) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_000, fv_syn_c0] using (nb071_compact_fv_empty_0022)

theorem nb071_wpp_notmem_0049 (x : Var) : x ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb071_compact_fv_empty_0023 x)

theorem nb071_wpp_notmem_0050 : (nb071_alpha_dummy_003) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_003, fv_syn_c0] using (nb071_compact_fv_empty_0024)

theorem nb071_wpp_notmem_0051 (x : Var) : (nb071_alpha_dummy_004 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_004, fv_syn_c0] using (nb071_compact_fv_empty_0025 x)

theorem nb071_compact_envfresh_0001 (x : Var) : TEnvFresh [((nb071_alpha_dummy_021), (nb071_alpha_dummy_024 x)), ((nb071_alpha_dummy_020), (nb071_alpha_dummy_023 x)), ((nb071_alpha_dummy_019), (nb071_alpha_dummy_022 x)), ((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)), ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)), ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_011), (nb071_alpha_dummy_012 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb071_alpha_dummy_021) (nb071_alpha_dummy_024 x) (nb071_wpp_notmem_0026) (nb071_wpp_notmem_0027 x) (TEnvFresh.consFresh (nb071_alpha_dummy_020) (nb071_alpha_dummy_023 x) (nb071_wpp_notmem_0028) (nb071_wpp_notmem_0029 x) (TEnvFresh.consFresh (nb071_alpha_dummy_019) (nb071_alpha_dummy_022 x) (nb071_wpp_notmem_0030) (nb071_wpp_notmem_0031 x) (TEnvFresh.consFresh (nb071_alpha_dummy_017) (nb071_alpha_dummy_018 x) (nb071_wpp_notmem_0032) (nb071_wpp_notmem_0033 x) (TEnvFresh.consFresh (nb071_alpha_dummy_013) (nb071_alpha_dummy_015 x) (nb071_wpp_notmem_0034) (nb071_wpp_notmem_0035 x) (TEnvFresh.consFresh (nb071_alpha_dummy_014) (nb071_alpha_dummy_016 x) (nb071_wpp_notmem_0036) (nb071_wpp_notmem_0037 x) (TEnvFresh.consFresh (nb071_alpha_dummy_006) (nb071_alpha_dummy_008 x) (nb071_wpp_notmem_0038) (nb071_wpp_notmem_0039 x) (TEnvFresh.consFresh (nb071_alpha_dummy_005) (nb071_alpha_dummy_007 x) (nb071_wpp_notmem_0040) (nb071_wpp_notmem_0041 x) (TEnvFresh.consFresh (nb071_alpha_dummy_011) (nb071_alpha_dummy_012 x) (nb071_wpp_notmem_0042) (nb071_wpp_notmem_0043 x) (TEnvFresh.consFresh (nb071_alpha_dummy_009) (nb071_alpha_dummy_010 x) (nb071_wpp_notmem_0044) (nb071_wpp_notmem_0045 x) (TEnvFresh.consFresh (nb071_alpha_dummy_001) (nb071_alpha_dummy_002 x) (nb071_wpp_notmem_0046) (nb071_wpp_notmem_0047 x) (TEnvFresh.consFresh (nb071_alpha_dummy_000) x (nb071_wpp_notmem_0048) (nb071_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb071_alpha_dummy_003) (nb071_alpha_dummy_004 x) (nb071_wpp_notmem_0050) (nb071_wpp_notmem_0051 x) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))

noncomputable def nb071_wpp_refl_0001 (x : Var) : TReflOn [((nb071_alpha_dummy_021), (nb071_alpha_dummy_024 x)), ((nb071_alpha_dummy_020), (nb071_alpha_dummy_023 x)), ((nb071_alpha_dummy_019), (nb071_alpha_dummy_022 x)), ((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)), ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)), ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_011), (nb071_alpha_dummy_012 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb071_compact_envfresh_0001 x)

noncomputable def nb071_split_alpha_0000 (x : Var) : TAlphaWff [((nb071_alpha_dummy_021), (nb071_alpha_dummy_024 x)), ((nb071_alpha_dummy_020), (nb071_alpha_dummy_023 x)), ((nb071_alpha_dummy_019), (nb071_alpha_dummy_022 x)), ((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)), ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)), ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_011), (nb071_alpha_dummy_012 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb071_alpha_dummy_020)) (Class.cv (nb071_alpha_dummy_021))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb071_alpha_dummy_019)) (syn_cun (Class.cv (nb071_alpha_dummy_020)) (Class.cv (nb071_alpha_dummy_021)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb071_alpha_dummy_023 x)) (Class.cv (nb071_alpha_dummy_024 x))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb071_alpha_dummy_022 x)) (syn_cun (Class.cv (nb071_alpha_dummy_023 x)) (Class.cv (nb071_alpha_dummy_024 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0021 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0019 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0025 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0023 x) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0021 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0019 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0025 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0023 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb071_alpha_dummy_021), (nb071_alpha_dummy_024 x)), ((nb071_alpha_dummy_020), (nb071_alpha_dummy_023 x)), ((nb071_alpha_dummy_019), (nb071_alpha_dummy_022 x)), ((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)), ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)), ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_011), (nb071_alpha_dummy_012 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] (syn_c0) (nb071_wpp_refl_0001 x))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0029 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0027 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0029 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0027 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0033 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0031 x) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0033 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0031 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb071_wpp_notmem_0052 : (nb071_alpha_dummy_017) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_017, fv_syn_cnnc] using (nb071_compact_fv_empty_0006)

theorem nb071_wpp_notmem_0053 (x : Var) : (nb071_alpha_dummy_018 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_018, fv_syn_cnnc] using (nb071_compact_fv_empty_0007 x)

theorem nb071_wpp_notmem_0054 : (nb071_alpha_dummy_013) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_013, fv_syn_cnnc] using (nb071_compact_fv_empty_0008)

theorem nb071_wpp_notmem_0055 (x : Var) : (nb071_alpha_dummy_015 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_015, fv_syn_cnnc] using (nb071_compact_fv_empty_0009 x)

theorem nb071_wpp_notmem_0056 : (nb071_alpha_dummy_014) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_014, fv_syn_cnnc] using (nb071_compact_fv_empty_0010)

theorem nb071_wpp_notmem_0057 (x : Var) : (nb071_alpha_dummy_016 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_016, fv_syn_cnnc] using (nb071_compact_fv_empty_0011 x)

theorem nb071_wpp_notmem_0058 : (nb071_alpha_dummy_006) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_006, fv_syn_cnnc] using (nb071_compact_fv_empty_0012)

theorem nb071_wpp_notmem_0059 (x : Var) : (nb071_alpha_dummy_008 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_008, fv_syn_cnnc] using (nb071_compact_fv_empty_0013 x)

theorem nb071_wpp_notmem_0060 : (nb071_alpha_dummy_005) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_005, fv_syn_cnnc] using (nb071_compact_fv_empty_0014)

theorem nb071_wpp_notmem_0061 (x : Var) : (nb071_alpha_dummy_007 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_007, fv_syn_cnnc] using (nb071_compact_fv_empty_0015 x)

theorem nb071_wpp_notmem_0062 : (nb071_alpha_dummy_011) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_011, fv_syn_cnnc] using (nb071_compact_fv_empty_0016)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
