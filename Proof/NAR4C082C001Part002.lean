import NAR4C082C001Part001

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

theorem nb082_fresh_075 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_059 A B R) ∉ (((syn_csn (Class.cv (nb082_alpha_dummy_050 A B R)))).fv) := by
  simpa only [nb082_alpha_dummy_059] using freshVar_not_mem (((syn_csn (Class.cv (nb082_alpha_dummy_050 A B R)))).fv) 0

theorem nb082_fresh_076 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_069 A B R) ∉ (((syn_csn (Class.cv (nb082_alpha_dummy_050 A B R)))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_050 A B R)))).fv) := by
  simpa only [nb082_alpha_dummy_069] using freshVar_not_mem (((syn_csn (Class.cv (nb082_alpha_dummy_050 A B R)))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_050 A B R)))).fv) 0

theorem nb082_fresh_077 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_072 A B R p) ∉ (((syn_csn (Class.cv (nb082_alpha_dummy_051 A B R p)))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_051 A B R p)))).fv) := by
  simpa only [nb082_alpha_dummy_072] using freshVar_not_mem (((syn_csn (Class.cv (nb082_alpha_dummy_051 A B R p)))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_051 A B R p)))).fv) 0

theorem nb082_fresh_078 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_060 A B R p) ∉ (((syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p)))).fv) := by
  simpa only [nb082_alpha_dummy_060] using freshVar_not_mem (((syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p)))).fv) 0

theorem nb082_fresh_079 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_070 A B R p) ∉ (((syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p)))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p)))).fv) := by
  simpa only [nb082_alpha_dummy_070] using freshVar_not_mem (((syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p)))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p)))).fv) 0

theorem nb082_fresh_080 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_063 A B R) ∉ (((syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_050 A B R)) (Class.cv (nb082_alpha_dummy_049 A B R))))).fv ∪ ((syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_050 A B R)) (Class.cv (nb082_alpha_dummy_049 A B R))))).fv) := by
  simpa only [nb082_alpha_dummy_063] using freshVar_not_mem (((syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_050 A B R)) (Class.cv (nb082_alpha_dummy_049 A B R))))).fv ∪ ((syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_050 A B R)) (Class.cv (nb082_alpha_dummy_049 A B R))))).fv) 0

theorem nb082_fresh_081 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_064 A B R p) ∉ (((syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_052 A B R p)) (Class.cv (nb082_alpha_dummy_051 A B R p))))).fv ∪ ((syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_052 A B R p)) (Class.cv (nb082_alpha_dummy_051 A B R p))))).fv) := by
  simpa only [nb082_alpha_dummy_064] using freshVar_not_mem (((syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_052 A B R p)) (Class.cv (nb082_alpha_dummy_051 A B R p))))).fv ∪ ((syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_052 A B R p)) (Class.cv (nb082_alpha_dummy_051 A B R p))))).fv) 0

theorem nb082_fresh_082 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_057 A B R) ∉ (((syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_050 A B R))))).fv ∪ ((syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_050 A B R))))).fv) := by
  simpa only [nb082_alpha_dummy_057] using freshVar_not_mem (((syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_050 A B R))))).fv ∪ ((syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_050 A B R))))).fv) 0

theorem nb082_fresh_083 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_058 A B R p) ∉ (((syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p))))).fv ∪ ((syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p))))).fv) := by
  simpa only [nb082_alpha_dummy_058] using freshVar_not_mem (((syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p))))).fv ∪ ((syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p))))).fv) 0

theorem nb082_fresh_084 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_000 A B R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv) := by
  simpa only [nb082_alpha_dummy_000] using freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv) 0

theorem nb082_fresh_085 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_001 A B R) ∉ (({(nb082_alpha_dummy_000 A B R)} : Finset Var) ∪ ((syn_cxpk B B)).fv ∪ ((syn_cfdminvalp R A B (Class.cv (nb082_alpha_dummy_000 A B R)))).fv) := by
  simpa only [nb082_alpha_dummy_001] using freshVar_not_mem (({(nb082_alpha_dummy_000 A B R)} : Finset Var) ∪ ((syn_cxpk B B)).fv ∪ ((syn_cfdminvalp R A B (Class.cv (nb082_alpha_dummy_000 A B R)))).fv) 0

theorem nb082_fresh_086 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_003 A B R) ∉ (({(nb082_alpha_dummy_000 A B R)} : Finset Var) ∪ ({(nb082_alpha_dummy_001 A B R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb082_alpha_dummy_000 A B R)) (syn_cxpk B B)) (Wff.classEq (Class.cv (nb082_alpha_dummy_001 A B R)) (syn_cfdminvalp R A B (Class.cv (nb082_alpha_dummy_000 A B R)))))).fv) := by
  simpa only [nb082_alpha_dummy_003] using freshVar_not_mem (({(nb082_alpha_dummy_000 A B R)} : Finset Var) ∪ ({(nb082_alpha_dummy_001 A B R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb082_alpha_dummy_000 A B R)) (syn_cxpk B B)) (Wff.classEq (Class.cv (nb082_alpha_dummy_001 A B R)) (syn_cfdminvalp R A B (Class.cv (nb082_alpha_dummy_000 A B R)))))).fv) 0

theorem nb082_fresh_087 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_002 A B R p) ∉ (({p} : Finset Var) ∪ ((syn_cxpk B B)).fv ∪ ((syn_cfdminvalp R A B (Class.cv p))).fv) := by
  simpa only [nb082_alpha_dummy_002] using freshVar_not_mem (({p} : Finset Var) ∪ ((syn_cxpk B B)).fv ∪ ((syn_cfdminvalp R A B (Class.cv p))).fv) 0

theorem nb082_fresh_088 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_004 A B R p) ∉ (({p} : Finset Var) ∪ ({(nb082_alpha_dummy_002 A B R p)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv p) (syn_cxpk B B)) (Wff.classEq (Class.cv (nb082_alpha_dummy_002 A B R p)) (syn_cfdminvalp R A B (Class.cv p))))).fv) := by
  simpa only [nb082_alpha_dummy_004] using freshVar_not_mem (({p} : Finset Var) ∪ ({(nb082_alpha_dummy_002 A B R p)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv p) (syn_cxpk B B)) (Wff.classEq (Class.cv (nb082_alpha_dummy_002 A B R p)) (syn_cfdminvalp R A B (Class.cv p))))).fv) 0

theorem nb082_support_mem_0000 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_000 A B R) ∈ (({(nb082_alpha_dummy_000 A B R)} : Finset Var) ∪ ({(nb082_alpha_dummy_001 A B R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb082_alpha_dummy_000 A B R)) (syn_cxpk B B)) (Wff.classEq (Class.cv (nb082_alpha_dummy_001 A B R)) (syn_cfdminvalp R A B (Class.cv (nb082_alpha_dummy_000 A B R)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0001 (A : Class) (B : Class) (R : Class) (p : Var) : p ∈ (({p} : Finset Var) ∪ ({(nb082_alpha_dummy_002 A B R p)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv p) (syn_cxpk B B)) (Wff.classEq (Class.cv (nb082_alpha_dummy_002 A B R p)) (syn_cfdminvalp R A B (Class.cv p))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0002 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_001 A B R) ∈ (({(nb082_alpha_dummy_000 A B R)} : Finset Var) ∪ ({(nb082_alpha_dummy_001 A B R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb082_alpha_dummy_000 A B R)) (syn_cxpk B B)) (Wff.classEq (Class.cv (nb082_alpha_dummy_001 A B R)) (syn_cfdminvalp R A B (Class.cv (nb082_alpha_dummy_000 A B R)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0003 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_002 A B R p) ∈ (({p} : Finset Var) ∪ ({(nb082_alpha_dummy_002 A B R p)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv p) (syn_cxpk B B)) (Wff.classEq (Class.cv (nb082_alpha_dummy_002 A B R p)) (syn_cfdminvalp R A B (Class.cv p))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0004 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_000 A B R) ∈ (({(nb082_alpha_dummy_000 A B R)} : Finset Var) ∪ ((syn_cxpk B B)).fv ∪ ((syn_cfdminvalp R A B (Class.cv (nb082_alpha_dummy_000 A B R)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0005 (A : Class) (B : Class) (R : Class) (p : Var) : p ∈ (({p} : Finset Var) ∪ ((syn_cxpk B B)).fv ∪ ((syn_cfdminvalp R A B (Class.cv p))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0006 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_000 A B R) ∈ (((Class.cv (nb082_alpha_dummy_000 A B R))).fv ∪ ((Class.cv (nb082_alpha_dummy_001 A B R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0007 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_000 A B R) ∈ (((syn_ccompl (Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_001 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0006 A B R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0006 A B R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb082_support_mem_0008 (A : Class) (B : Class) (R : Class) (p : Var) : p ∈ (((Class.cv p)).fv ∪ ((Class.cv (nb082_alpha_dummy_002 A B R p))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0009 (A : Class) (B : Class) (R : Class) (p : Var) : p ∈ (((syn_ccompl (Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv p) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p)))))))).fv ∪ ((syn_ccompl (Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv (nb082_alpha_dummy_002 A B R p)) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0008 A B R p) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0008 A B R p) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb082_support_mem_0010 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_000 A B R) ∈ (((Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))))))).fv ∪ ((Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0006 A B R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0006 A B R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb082_support_mem_0011 (A : Class) (B : Class) (R : Class) (p : Var) : p ∈ (((Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv p) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))))))).fv ∪ ((Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv p) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0008 A B R p) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0008 A B R p) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb082_support_mem_0012 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_006 A B R) ∈ (((Class.cv (nb082_alpha_dummy_006 A B R))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0013 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_008 A B R p) ∈ (((Class.cv (nb082_alpha_dummy_008 A B R p))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0014 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_013 A B R) ∈ (((Wff.classMem (Class.cv (nb082_alpha_dummy_013 A B R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb082_alpha_dummy_013 A B R)) (syn_c1c))).fv ∪ ((Class.cv (nb082_alpha_dummy_013 A B R))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0015 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_015 A B R p) ∈ (((Wff.classMem (Class.cv (nb082_alpha_dummy_015 A B R p)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb082_alpha_dummy_015 A B R p)) (syn_c1c))).fv ∪ ((Class.cv (nb082_alpha_dummy_015 A B R p))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0016 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_013 A B R) ∈ (((Class.cv (nb082_alpha_dummy_013 A B R))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0017 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_015 A B R p) ∈ (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0018 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_020 A B R) ∈ (((syn_cnin (Class.cv (nb082_alpha_dummy_020 A B R)) (Class.cv (nb082_alpha_dummy_021 A B R)))).fv ∪ ((syn_cnin (Class.cv (nb082_alpha_dummy_020 A B R)) (Class.cv (nb082_alpha_dummy_021 A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0019 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_023 A B R p) ∈ (((syn_cnin (Class.cv (nb082_alpha_dummy_023 A B R p)) (Class.cv (nb082_alpha_dummy_024 A B R p)))).fv ∪ ((syn_cnin (Class.cv (nb082_alpha_dummy_023 A B R p)) (Class.cv (nb082_alpha_dummy_024 A B R p)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0020 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_020 A B R) ∈ (((Class.cv (nb082_alpha_dummy_020 A B R))).fv ∪ ((Class.cv (nb082_alpha_dummy_021 A B R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0021 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_023 A B R p) ∈ (((Class.cv (nb082_alpha_dummy_023 A B R p))).fv ∪ ((Class.cv (nb082_alpha_dummy_024 A B R p))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0022 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_021 A B R) ∈ (((syn_cnin (Class.cv (nb082_alpha_dummy_020 A B R)) (Class.cv (nb082_alpha_dummy_021 A B R)))).fv ∪ ((syn_cnin (Class.cv (nb082_alpha_dummy_020 A B R)) (Class.cv (nb082_alpha_dummy_021 A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0023 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_024 A B R p) ∈ (((syn_cnin (Class.cv (nb082_alpha_dummy_023 A B R p)) (Class.cv (nb082_alpha_dummy_024 A B R p)))).fv ∪ ((syn_cnin (Class.cv (nb082_alpha_dummy_023 A B R p)) (Class.cv (nb082_alpha_dummy_024 A B R p)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0024 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_021 A B R) ∈ (((Class.cv (nb082_alpha_dummy_020 A B R))).fv ∪ ((Class.cv (nb082_alpha_dummy_021 A B R))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0025 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_024 A B R p) ∈ (((Class.cv (nb082_alpha_dummy_023 A B R p))).fv ∪ ((Class.cv (nb082_alpha_dummy_024 A B R p))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0026 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_020 A B R) ∈ (((syn_ccompl (Class.cv (nb082_alpha_dummy_020 A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb082_alpha_dummy_021 A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0027 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_023 A B R p) ∈ (((syn_ccompl (Class.cv (nb082_alpha_dummy_023 A B R p)))).fv ∪ ((syn_ccompl (Class.cv (nb082_alpha_dummy_024 A B R p)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0028 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_020 A B R) ∈ (((Class.cv (nb082_alpha_dummy_020 A B R))).fv ∪ ((Class.cv (nb082_alpha_dummy_020 A B R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0029 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_023 A B R p) ∈ (((Class.cv (nb082_alpha_dummy_023 A B R p))).fv ∪ ((Class.cv (nb082_alpha_dummy_023 A B R p))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0030 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_021 A B R) ∈ (((syn_ccompl (Class.cv (nb082_alpha_dummy_020 A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb082_alpha_dummy_021 A B R)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0031 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_024 A B R p) ∈ (((syn_ccompl (Class.cv (nb082_alpha_dummy_023 A B R p)))).fv ∪ ((syn_ccompl (Class.cv (nb082_alpha_dummy_024 A B R p)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0032 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_021 A B R) ∈ (((Class.cv (nb082_alpha_dummy_021 A B R))).fv ∪ ((Class.cv (nb082_alpha_dummy_021 A B R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0033 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_024 A B R p) ∈ (((Class.cv (nb082_alpha_dummy_024 A B R p))).fv ∪ ((Class.cv (nb082_alpha_dummy_024 A B R p))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0034 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_001 A B R) ∈ (((Class.cv (nb082_alpha_dummy_000 A B R))).fv ∪ ((Class.cv (nb082_alpha_dummy_001 A B R))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0035 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_001 A B R) ∈ (((syn_ccompl (Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_001 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0034 A B R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0034 A B R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb082_support_mem_0036 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_002 A B R p) ∈ (((Class.cv p)).fv ∪ ((Class.cv (nb082_alpha_dummy_002 A B R p))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0037 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_002 A B R p) ∈ (((syn_ccompl (Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv p) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p)))))))).fv ∪ ((syn_ccompl (Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv (nb082_alpha_dummy_002 A B R p)) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0036 A B R p) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0036 A B R p) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb082_support_mem_0038 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_001 A B R) ∈ (((Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_001 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R) (Class.cv (nb082_alpha_dummy_001 A B R)) (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0034 A B R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0034 A B R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb082_support_mem_0039 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_002 A B R p) ∈ (((Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv (nb082_alpha_dummy_002 A B R p)) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p) (Class.cv (nb082_alpha_dummy_002 A B R p)) (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p)) (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0036 A B R p) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0036 A B R p) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb082_support_mem_0040 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_006 A B R) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0041 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_008 A B R p) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0042 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_006 A B R) ∈ (((syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R)))).fv ∪ ((syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0043 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_008 A B R p) ∈ (((syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p)))).fv ∪ ((syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0044 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_000 A B R) ∈ (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv) := by
  rw [fv_syn_cin]
  apply Finset.mem_union_left
  rw [fv_syn_cimak]
  apply Finset.mem_union_right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0045 (A : Class) (B : Class) (R : Class) (p : Var) : p ∈ (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))) (syn_c1c))).fv) := by
  rw [fv_syn_cin]
  apply Finset.mem_union_left
  rw [fv_syn_cimak]
  apply Finset.mem_union_right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0046 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_000 A B R) ∈ (((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv ∪ ((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_cimak]
  apply Finset.mem_union_right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0047 (A : Class) (B : Class) (R : Class) (p : Var) : p ∈ (((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))) (syn_c1c))).fv ∪ ((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))) (syn_c1c))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_cimak]
  apply Finset.mem_union_right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0048 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_000 A B R) ∈ (((syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R))))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cimak]
  apply Finset.mem_union_right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0049 (A : Class) (B : Class) (R : Class) (p : Var) : p ∈ (((syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cimak]
  apply Finset.mem_union_right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0050 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_000 A B R) ∈ (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0051 (A : Class) (B : Class) (R : Class) (p : Var) : p ∈ (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn (Class.cv p))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0052 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_000 A B R) ∈ (((Class.cv (nb082_alpha_dummy_000 A B R))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0053 (p : Var) : p ∈ (((Class.cv p)).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0054 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_050 A B R) ∈ (((syn_ccompl (syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_050 A B R)))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_050 A B R)) (Class.cv (nb082_alpha_dummy_049 A B R)))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0055 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_052 A B R p) ∈ (((syn_ccompl (syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p)))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_052 A B R p)) (Class.cv (nb082_alpha_dummy_051 A B R p)))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0056 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_050 A B R) ∈ (((syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_050 A B R))))).fv ∪ ((syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_050 A B R))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0057 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_052 A B R p) ∈ (((syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p))))).fv ∪ ((syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0058 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_050 A B R) ∈ (((syn_csn (Class.cv (nb082_alpha_dummy_050 A B R)))).fv) := by
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0059 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_052 A B R p) ∈ (((syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p)))).fv) := by
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0060 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_050 A B R) ∈ (((Class.cv (nb082_alpha_dummy_050 A B R))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0061 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_052 A B R p) ∈ (((Class.cv (nb082_alpha_dummy_052 A B R p))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0062 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_050 A B R) ∈ (((syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_050 A B R)) (Class.cv (nb082_alpha_dummy_049 A B R))))).fv ∪ ((syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_050 A B R)) (Class.cv (nb082_alpha_dummy_049 A B R))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0063 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_052 A B R p) ∈ (((syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_052 A B R p)) (Class.cv (nb082_alpha_dummy_051 A B R p))))).fv ∪ ((syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_052 A B R p)) (Class.cv (nb082_alpha_dummy_051 A B R p))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0064 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_050 A B R) ∈ (((syn_cpr (Class.cv (nb082_alpha_dummy_050 A B R)) (Class.cv (nb082_alpha_dummy_049 A B R)))).fv) := by
  rw [fv_syn_cpr]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0065 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_052 A B R p) ∈ (((syn_cpr (Class.cv (nb082_alpha_dummy_052 A B R p)) (Class.cv (nb082_alpha_dummy_051 A B R p)))).fv) := by
  rw [fv_syn_cpr]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0066 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_050 A B R) ∈ (((syn_ccompl (syn_csn (Class.cv (nb082_alpha_dummy_050 A B R))))).fv ∪ ((syn_ccompl (syn_csn (Class.cv (nb082_alpha_dummy_049 A B R))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0067 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_052 A B R p) ∈ (((syn_ccompl (syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p))))).fv ∪ ((syn_ccompl (syn_csn (Class.cv (nb082_alpha_dummy_051 A B R p))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0068 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_050 A B R) ∈ (((syn_csn (Class.cv (nb082_alpha_dummy_050 A B R)))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_050 A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0069 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_052 A B R p) ∈ (((syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p)))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0070 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_049 A B R) ∈ (((syn_ccompl (syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_050 A B R)))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_050 A B R)) (Class.cv (nb082_alpha_dummy_049 A B R)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0071 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_051 A B R p) ∈ (((syn_ccompl (syn_csn (syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p)))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_052 A B R p)) (Class.cv (nb082_alpha_dummy_051 A B R p)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0072 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_049 A B R) ∈ (((syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_050 A B R)) (Class.cv (nb082_alpha_dummy_049 A B R))))).fv ∪ ((syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_050 A B R)) (Class.cv (nb082_alpha_dummy_049 A B R))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0073 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_051 A B R p) ∈ (((syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_052 A B R p)) (Class.cv (nb082_alpha_dummy_051 A B R p))))).fv ∪ ((syn_csn (syn_cpr (Class.cv (nb082_alpha_dummy_052 A B R p)) (Class.cv (nb082_alpha_dummy_051 A B R p))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0074 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_049 A B R) ∈ (((syn_cpr (Class.cv (nb082_alpha_dummy_050 A B R)) (Class.cv (nb082_alpha_dummy_049 A B R)))).fv) := by
  rw [fv_syn_cpr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0075 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_051 A B R p) ∈ (((syn_cpr (Class.cv (nb082_alpha_dummy_052 A B R p)) (Class.cv (nb082_alpha_dummy_051 A B R p)))).fv) := by
  rw [fv_syn_cpr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0076 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_049 A B R) ∈ (((syn_ccompl (syn_csn (Class.cv (nb082_alpha_dummy_050 A B R))))).fv ∪ ((syn_ccompl (syn_csn (Class.cv (nb082_alpha_dummy_049 A B R))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0077 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_051 A B R p) ∈ (((syn_ccompl (syn_csn (Class.cv (nb082_alpha_dummy_052 A B R p))))).fv ∪ ((syn_ccompl (syn_csn (Class.cv (nb082_alpha_dummy_051 A B R p))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0078 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_049 A B R) ∈ (((syn_csn (Class.cv (nb082_alpha_dummy_049 A B R)))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_049 A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0079 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_051 A B R p) ∈ (((syn_csn (Class.cv (nb082_alpha_dummy_051 A B R p)))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_051 A B R p)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0080 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_049 A B R) ∈ (((Class.cv (nb082_alpha_dummy_049 A B R))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_support_mem_0081 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_051 A B R p) ∈ (((Class.cv (nb082_alpha_dummy_051 A B R p))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb082_compact_fv_empty_0000 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_021 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0000 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_021 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_021, fv_syn_c1c] using (nb082_compact_fv_empty_0000 A B R)

theorem nb082_compact_fv_empty_0001 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_024 A B R p) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0001 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_024 A B R p) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_024, fv_syn_c1c] using (nb082_compact_fv_empty_0001 A B R p)

theorem nb082_compact_fv_empty_0002 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_020 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0002 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_020 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_020, fv_syn_c1c] using (nb082_compact_fv_empty_0002 A B R)

theorem nb082_compact_fv_empty_0003 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_023 A B R p) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0003 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_023 A B R p) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_023, fv_syn_c1c] using (nb082_compact_fv_empty_0003 A B R p)

theorem nb082_compact_fv_empty_0004 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_019 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0004 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_019 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_019, fv_syn_c1c] using (nb082_compact_fv_empty_0004 A B R)

theorem nb082_compact_fv_empty_0005 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_022 A B R p) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0005 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_022 A B R p) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_022, fv_syn_c1c] using (nb082_compact_fv_empty_0005 A B R p)

theorem nb082_compact_fv_empty_0006 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_017 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0006 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_017 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_017, fv_syn_c1c] using (nb082_compact_fv_empty_0006 A B R)

theorem nb082_compact_fv_empty_0007 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_018 A B R p) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0007 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_018 A B R p) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_018, fv_syn_c1c] using (nb082_compact_fv_empty_0007 A B R p)

theorem nb082_compact_fv_empty_0008 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_013 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0008 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_013 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_013, fv_syn_c1c] using (nb082_compact_fv_empty_0008 A B R)

theorem nb082_compact_fv_empty_0009 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_015 A B R p) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0009 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_015 A B R p) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_015, fv_syn_c1c] using (nb082_compact_fv_empty_0009 A B R p)

theorem nb082_compact_fv_empty_0010 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_014 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0010 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_014 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_014, fv_syn_c1c] using (nb082_compact_fv_empty_0010 A B R)

theorem nb082_compact_fv_empty_0011 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_016 A B R p) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0011 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_016 A B R p) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_016, fv_syn_c1c] using (nb082_compact_fv_empty_0011 A B R p)

theorem nb082_compact_fv_empty_0012 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_006 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0012 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_006 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_006, fv_syn_c1c] using (nb082_compact_fv_empty_0012 A B R)

theorem nb082_compact_fv_empty_0013 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_008 A B R p) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0013 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_008 A B R p) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_008, fv_syn_c1c] using (nb082_compact_fv_empty_0013 A B R p)

theorem nb082_compact_fv_empty_0014 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_005 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0014 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_005 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_005, fv_syn_c1c] using (nb082_compact_fv_empty_0014 A B R)

theorem nb082_compact_fv_empty_0015 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_007 A B R p) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0015 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_007 A B R p) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_007, fv_syn_c1c] using (nb082_compact_fv_empty_0015 A B R p)

theorem nb082_compact_fv_empty_0016 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_011 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0016 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_011 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_011, fv_syn_c1c] using (nb082_compact_fv_empty_0016 A B R)

theorem nb082_compact_fv_empty_0017 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_012 A B R p) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0017 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_012 A B R p) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_012, fv_syn_c1c] using (nb082_compact_fv_empty_0017 A B R p)

theorem nb082_compact_fv_empty_0018 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_009 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0018 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_009 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_009, fv_syn_c1c] using (nb082_compact_fv_empty_0018 A B R)

theorem nb082_compact_fv_empty_0019 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_010 A B R p) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0019 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_010 A B R p) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_010, fv_syn_c1c] using (nb082_compact_fv_empty_0019 A B R p)

theorem nb082_compact_fv_empty_0020 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_001 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0020 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_001 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_001, fv_syn_c1c] using (nb082_compact_fv_empty_0020 A B R)

theorem nb082_compact_fv_empty_0021 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_002 A B R p) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0021 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_002 A B R p) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_002, fv_syn_c1c] using (nb082_compact_fv_empty_0021 A B R p)

theorem nb082_compact_fv_empty_0022 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_000 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0022 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_000 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_000, fv_syn_c1c] using (nb082_compact_fv_empty_0022 A B R)

theorem nb082_compact_fv_empty_0023 (p : Var) : p ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0023 (p : Var) : p ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb082_compact_fv_empty_0023 p)

theorem nb082_compact_fv_empty_0024 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_003 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0024 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_003 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_003, fv_syn_c1c] using (nb082_compact_fv_empty_0024 A B R)

theorem nb082_compact_fv_empty_0025 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_004 A B R p) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0025 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_004 A B R p) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_004, fv_syn_c1c] using (nb082_compact_fv_empty_0025 A B R p)

theorem nb082_compact_envfresh_0000 (A : Class) (B : Class) (R : Class) (p : Var) : TEnvFresh [((nb082_alpha_dummy_021 A B R), (nb082_alpha_dummy_024 A B R p)), ((nb082_alpha_dummy_020 A B R), (nb082_alpha_dummy_023 A B R p)), ((nb082_alpha_dummy_019 A B R), (nb082_alpha_dummy_022 A B R p)), ((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)), ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)), ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)), ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)), ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)), ((nb082_alpha_dummy_011 A B R), (nb082_alpha_dummy_012 A B R p)), ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)), ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)), ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb082_alpha_dummy_021 A B R) (nb082_alpha_dummy_024 A B R p) (nb082_wpp_notmem_0000 A B R) (nb082_wpp_notmem_0001 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_020 A B R) (nb082_alpha_dummy_023 A B R p) (nb082_wpp_notmem_0002 A B R) (nb082_wpp_notmem_0003 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_019 A B R) (nb082_alpha_dummy_022 A B R p) (nb082_wpp_notmem_0004 A B R) (nb082_wpp_notmem_0005 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_017 A B R) (nb082_alpha_dummy_018 A B R p) (nb082_wpp_notmem_0006 A B R) (nb082_wpp_notmem_0007 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_013 A B R) (nb082_alpha_dummy_015 A B R p) (nb082_wpp_notmem_0008 A B R) (nb082_wpp_notmem_0009 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_014 A B R) (nb082_alpha_dummy_016 A B R p) (nb082_wpp_notmem_0010 A B R) (nb082_wpp_notmem_0011 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_006 A B R) (nb082_alpha_dummy_008 A B R p) (nb082_wpp_notmem_0012 A B R) (nb082_wpp_notmem_0013 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_005 A B R) (nb082_alpha_dummy_007 A B R p) (nb082_wpp_notmem_0014 A B R) (nb082_wpp_notmem_0015 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_011 A B R) (nb082_alpha_dummy_012 A B R p) (nb082_wpp_notmem_0016 A B R) (nb082_wpp_notmem_0017 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_009 A B R) (nb082_alpha_dummy_010 A B R p) (nb082_wpp_notmem_0018 A B R) (nb082_wpp_notmem_0019 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_001 A B R) (nb082_alpha_dummy_002 A B R p) (nb082_wpp_notmem_0020 A B R) (nb082_wpp_notmem_0021 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_000 A B R) p (nb082_wpp_notmem_0022 A B R) (nb082_wpp_notmem_0023 p) (TEnvFresh.consFresh (nb082_alpha_dummy_003 A B R) (nb082_alpha_dummy_004 A B R p) (nb082_wpp_notmem_0024 A B R) (nb082_wpp_notmem_0025 A B R p) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))

noncomputable def nb082_wpp_refl_0000 (A : Class) (B : Class) (R : Class) (p : Var) : TReflOn [((nb082_alpha_dummy_021 A B R), (nb082_alpha_dummy_024 A B R p)), ((nb082_alpha_dummy_020 A B R), (nb082_alpha_dummy_023 A B R p)), ((nb082_alpha_dummy_019 A B R), (nb082_alpha_dummy_022 A B R p)), ((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)), ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)), ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)), ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)), ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)), ((nb082_alpha_dummy_011 A B R), (nb082_alpha_dummy_012 A B R p)), ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)), ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)), ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb082_compact_envfresh_0000 A B R p)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
