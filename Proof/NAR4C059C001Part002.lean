import NAR4C059C001Part001

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

theorem nb059_support_mem_0030 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_032 R S_cls) ∈ (((syn_ccompl (Class.cv (nb059_alpha_dummy_032 R S_cls)))).fv ∪ ((syn_ccompl (Class.cv (nb059_alpha_dummy_033 R S_cls)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0031 (R : Class) (a : Var) : (nb059_alpha_dummy_035 R a) ∈ (((syn_ccompl (Class.cv (nb059_alpha_dummy_035 R a)))).fv ∪ ((syn_ccompl (Class.cv (nb059_alpha_dummy_036 R a)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0032 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_032 R S_cls) ∈ (((Class.cv (nb059_alpha_dummy_032 R S_cls))).fv ∪ ((Class.cv (nb059_alpha_dummy_032 R S_cls))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0033 (R : Class) (a : Var) : (nb059_alpha_dummy_035 R a) ∈ (((Class.cv (nb059_alpha_dummy_035 R a))).fv ∪ ((Class.cv (nb059_alpha_dummy_035 R a))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0034 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_033 R S_cls) ∈ (((syn_ccompl (Class.cv (nb059_alpha_dummy_032 R S_cls)))).fv ∪ ((syn_ccompl (Class.cv (nb059_alpha_dummy_033 R S_cls)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0035 (R : Class) (a : Var) : (nb059_alpha_dummy_036 R a) ∈ (((syn_ccompl (Class.cv (nb059_alpha_dummy_035 R a)))).fv ∪ ((syn_ccompl (Class.cv (nb059_alpha_dummy_036 R a)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0036 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_033 R S_cls) ∈ (((Class.cv (nb059_alpha_dummy_033 R S_cls))).fv ∪ ((Class.cv (nb059_alpha_dummy_033 R S_cls))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0037 (R : Class) (a : Var) : (nb059_alpha_dummy_036 R a) ∈ (((Class.cv (nb059_alpha_dummy_036 R a))).fv ∪ ((Class.cv (nb059_alpha_dummy_036 R a))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0038 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_013 R S_cls) ∈ (((Class.cv (nb059_alpha_dummy_014 R S_cls))).fv ∪ ((Class.cv (nb059_alpha_dummy_013 R S_cls))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0039 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_013 R S_cls) ∈ (((syn_ccompl (Class.cab (nb059_alpha_dummy_017 R S_cls) (syn_wrex (nb059_alpha_dummy_018 R S_cls) (Class.cv (nb059_alpha_dummy_014 R S_cls)) (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls)) (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))))))).fv ∪ ((syn_ccompl (Class.cab (nb059_alpha_dummy_017 R S_cls) (syn_wrex (nb059_alpha_dummy_018 R S_cls) (Class.cv (nb059_alpha_dummy_013 R S_cls)) (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls)) (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0038 R S_cls) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0038 R S_cls) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb059_support_mem_0040 (R : Class) (a : Var) : (nb059_alpha_dummy_015 R a) ∈ (((Class.cv (nb059_alpha_dummy_016 R a))).fv ∪ ((Class.cv (nb059_alpha_dummy_015 R a))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0041 (R : Class) (a : Var) : (nb059_alpha_dummy_015 R a) ∈ (((syn_ccompl (Class.cab (nb059_alpha_dummy_019 R a) (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_016 R a)) (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a)) (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))))))).fv ∪ ((syn_ccompl (Class.cab (nb059_alpha_dummy_019 R a) (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_015 R a)) (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a)) (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0040 R a) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0040 R a) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb059_support_mem_0042 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_013 R S_cls) ∈ (((Class.cab (nb059_alpha_dummy_017 R S_cls) (syn_wrex (nb059_alpha_dummy_018 R S_cls) (Class.cv (nb059_alpha_dummy_013 R S_cls)) (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls)) (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb059_alpha_dummy_017 R S_cls) (syn_wrex (nb059_alpha_dummy_018 R S_cls) (Class.cv (nb059_alpha_dummy_013 R S_cls)) (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls)) (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0038 R S_cls) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0038 R S_cls) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb059_support_mem_0043 (R : Class) (a : Var) : (nb059_alpha_dummy_015 R a) ∈ (((Class.cab (nb059_alpha_dummy_019 R a) (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_015 R a)) (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a)) (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb059_alpha_dummy_019 R a) (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_015 R a)) (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a)) (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0040 R a) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0040 R a) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb059_support_mem_0044 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_018 R S_cls) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0045 (R : Class) (a : Var) : (nb059_alpha_dummy_020 R a) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0046 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_018 R S_cls) ∈ (((syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))).fv ∪ ((syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0047 (R : Class) (a : Var) : (nb059_alpha_dummy_020 R a) ∈ (((syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))).fv ∪ ((syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_focused_notmem_0000 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_007 R S_cls) ∉ S_cls.fv := by
  change freshVar ((S_cls).fv ∪ ((Class.cv (nb059_alpha_dummy_000 R S_cls))).fv) 0 ∉ S_cls.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (hu))

theorem nb059_wpp_notmem_0000 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_007 R S_cls) ∉ (S_cls).fv := by
  exact (nb059_focused_notmem_0000 R S_cls)

theorem nb059_focused_notmem_0001 (S_cls : Class) (a : Var) : (nb059_alpha_dummy_008 S_cls a) ∉ S_cls.fv := by
  change freshVar ((S_cls).fv ∪ ((Class.cv a)).fv) 0 ∉ S_cls.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (hu))

theorem nb059_wpp_notmem_0001 (S_cls : Class) (a : Var) : (nb059_alpha_dummy_008 S_cls a) ∉ (S_cls).fv := by
  exact (nb059_focused_notmem_0001 S_cls a)

theorem nb059_focused_notmem_0002 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_005 R S_cls) ∉ S_cls.fv := by
  change freshVar (((syn_cnin S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))).fv ∪ ((syn_cnin S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))).fv) 0 ∉ S_cls.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (((fv_syn_cnin S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls))).symm ▸ (Finset.mem_union_left _ (hu)))))

theorem nb059_wpp_notmem_0002 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_005 R S_cls) ∉ (S_cls).fv := by
  exact (nb059_focused_notmem_0002 R S_cls)

theorem nb059_focused_notmem_0003 (S_cls : Class) (a : Var) : (nb059_alpha_dummy_006 S_cls a) ∉ S_cls.fv := by
  change freshVar (((syn_cnin S_cls (Class.cv a))).fv ∪ ((syn_cnin S_cls (Class.cv a))).fv) 0 ∉ S_cls.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (((fv_syn_cnin S_cls (Class.cv a)).symm ▸ (Finset.mem_union_left _ (hu)))))

theorem nb059_wpp_notmem_0003 (S_cls : Class) (a : Var) : (nb059_alpha_dummy_006 S_cls a) ∉ (S_cls).fv := by
  exact (nb059_focused_notmem_0003 S_cls a)

theorem nb059_focused_notmem_0004 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_000 R S_cls) ∉ S_cls.fv := by
  change freshVar ((S_cls).fv ∪ (R).fv) 0 ∉ S_cls.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (hu))

theorem nb059_wpp_notmem_0004 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_000 R S_cls) ∉ (S_cls).fv := by
  exact (nb059_focused_notmem_0004 R S_cls)

theorem nb059_wpp_notmem_0005 (S_cls : Class) (a : Var) (dv_S_a : a ∉ S_cls.fv) : a ∉ (S_cls).fv := by
  exact dv_S_a

theorem nb059_focused_notmem_0005 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_002 R S_cls) ∉ S_cls.fv := by
  change freshVar (((Class.cab (nb059_alpha_dummy_000 R S_cls) (syn_wa (syn_wss S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls))) (syn_wss (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls))) (Class.cv (nb059_alpha_dummy_000 R S_cls)))))).fv) 1 ∉ S_cls.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun u hu => ((fv_class_cab (nb059_alpha_dummy_000 R S_cls) (syn_wa (syn_wss S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls))) (syn_wss (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls))) (Class.cv (nb059_alpha_dummy_000 R S_cls))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb059_focused_notmem_0004 R S_cls)) (h_eq ▸ hu)), (((fv_syn_wa (syn_wss S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls))) (syn_wss (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls))) (Class.cv (nb059_alpha_dummy_000 R S_cls)))).symm ▸ (Finset.mem_union_left _ (((fv_syn_wss S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls))).symm ▸ (Finset.mem_union_left _ (hu)))))))⟩)))

theorem nb059_wpp_notmem_0006 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_002 R S_cls) ∉ (S_cls).fv := by
  exact (nb059_focused_notmem_0005 R S_cls)

theorem nb059_focused_notmem_0006 (R : Class) (S_cls : Class) (a : Var) (dv_S_a : a ∉ S_cls.fv) : (nb059_alpha_dummy_004 R S_cls a) ∉ S_cls.fv := by
  change freshVar (((Class.cab a (syn_wa (syn_wss S_cls (Class.cv a)) (syn_wss (syn_cima R (Class.cv a)) (Class.cv a))))).fv) 1 ∉ S_cls.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun u hu => ((fv_class_cab a (syn_wa (syn_wss S_cls (Class.cv a)) (syn_wss (syn_cima R (Class.cv a)) (Class.cv a)))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => (dv_S_a) (h_eq ▸ hu)), (((fv_syn_wa (syn_wss S_cls (Class.cv a)) (syn_wss (syn_cima R (Class.cv a)) (Class.cv a))).symm ▸ (Finset.mem_union_left _ (((fv_syn_wss S_cls (Class.cv a)).symm ▸ (Finset.mem_union_left _ (hu)))))))⟩)))

theorem nb059_wpp_notmem_0007 (R : Class) (S_cls : Class) (a : Var) (dv_S_a : a ∉ S_cls.fv) : (nb059_alpha_dummy_004 R S_cls a) ∉ (S_cls).fv := by
  exact (nb059_focused_notmem_0006 R S_cls a dv_S_a)

theorem nb059_focused_notmem_0007 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_001 R S_cls) ∉ S_cls.fv := by
  change freshVar (((Class.cab (nb059_alpha_dummy_000 R S_cls) (syn_wa (syn_wss S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls))) (syn_wss (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls))) (Class.cv (nb059_alpha_dummy_000 R S_cls)))))).fv) 0 ∉ S_cls.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => ((fv_class_cab (nb059_alpha_dummy_000 R S_cls) (syn_wa (syn_wss S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls))) (syn_wss (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls))) (Class.cv (nb059_alpha_dummy_000 R S_cls))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb059_focused_notmem_0004 R S_cls)) (h_eq ▸ hu)), (((fv_syn_wa (syn_wss S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls))) (syn_wss (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls))) (Class.cv (nb059_alpha_dummy_000 R S_cls)))).symm ▸ (Finset.mem_union_left _ (((fv_syn_wss S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls))).symm ▸ (Finset.mem_union_left _ (hu)))))))⟩)))

theorem nb059_wpp_notmem_0008 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_001 R S_cls) ∉ (S_cls).fv := by
  exact (nb059_focused_notmem_0007 R S_cls)

theorem nb059_focused_notmem_0008 (R : Class) (S_cls : Class) (a : Var) (dv_S_a : a ∉ S_cls.fv) : (nb059_alpha_dummy_003 R S_cls a) ∉ S_cls.fv := by
  change freshVar (((Class.cab a (syn_wa (syn_wss S_cls (Class.cv a)) (syn_wss (syn_cima R (Class.cv a)) (Class.cv a))))).fv) 0 ∉ S_cls.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => ((fv_class_cab a (syn_wa (syn_wss S_cls (Class.cv a)) (syn_wss (syn_cima R (Class.cv a)) (Class.cv a)))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => (dv_S_a) (h_eq ▸ hu)), (((fv_syn_wa (syn_wss S_cls (Class.cv a)) (syn_wss (syn_cima R (Class.cv a)) (Class.cv a))).symm ▸ (Finset.mem_union_left _ (((fv_syn_wss S_cls (Class.cv a)).symm ▸ (Finset.mem_union_left _ (hu)))))))⟩)))

theorem nb059_wpp_notmem_0009 (R : Class) (S_cls : Class) (a : Var) (dv_S_a : a ∉ S_cls.fv) : (nb059_alpha_dummy_003 R S_cls a) ∉ (S_cls).fv := by
  exact (nb059_focused_notmem_0008 R S_cls a dv_S_a)

theorem nb059_compact_envfresh_0000 (R : Class) (S_cls : Class) (a : Var) (dv_S_a : a ∉ S_cls.fv) : TEnvFresh [((nb059_alpha_dummy_007 R S_cls), (nb059_alpha_dummy_008 S_cls a)), ((nb059_alpha_dummy_005 R S_cls), (nb059_alpha_dummy_006 S_cls a)), ((nb059_alpha_dummy_000 R S_cls), a), ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)), ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))] (S_cls).fv := by
  exact (TEnvFresh.consFresh (nb059_alpha_dummy_007 R S_cls) (nb059_alpha_dummy_008 S_cls a) (nb059_wpp_notmem_0000 R S_cls) (nb059_wpp_notmem_0001 S_cls a) (TEnvFresh.consFresh (nb059_alpha_dummy_005 R S_cls) (nb059_alpha_dummy_006 S_cls a) (nb059_wpp_notmem_0002 R S_cls) (nb059_wpp_notmem_0003 S_cls a) (TEnvFresh.consFresh (nb059_alpha_dummy_000 R S_cls) a (nb059_wpp_notmem_0004 R S_cls) (nb059_wpp_notmem_0005 S_cls a dv_S_a) (TEnvFresh.consFresh (nb059_alpha_dummy_002 R S_cls) (nb059_alpha_dummy_004 R S_cls a) (nb059_wpp_notmem_0006 R S_cls) (nb059_wpp_notmem_0007 R S_cls a dv_S_a) (TEnvFresh.consFresh (nb059_alpha_dummy_001 R S_cls) (nb059_alpha_dummy_003 R S_cls a) (nb059_wpp_notmem_0008 R S_cls) (nb059_wpp_notmem_0009 R S_cls a dv_S_a) (TEnvFresh.nil (S_cls).fv))))))

noncomputable def nb059_wpp_refl_0000 (R : Class) (S_cls : Class) (a : Var) (dv_S_a : a ∉ S_cls.fv) : TReflOn [((nb059_alpha_dummy_007 R S_cls), (nb059_alpha_dummy_008 S_cls a)), ((nb059_alpha_dummy_005 R S_cls), (nb059_alpha_dummy_006 S_cls a)), ((nb059_alpha_dummy_000 R S_cls), a), ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)), ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))] (S_cls).fv :=
  TEnvFresh.reflOn (nb059_compact_envfresh_0000 R S_cls a dv_S_a)

theorem nb059_compact_envfresh_0001 (R : Class) (S_cls : Class) (a : Var) (dv_S_a : a ∉ S_cls.fv) : TEnvFresh [((nb059_alpha_dummy_000 R S_cls), a), ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)), ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))] (S_cls).fv := by
  exact (TEnvFresh.consFresh (nb059_alpha_dummy_000 R S_cls) a (nb059_wpp_notmem_0004 R S_cls) (nb059_wpp_notmem_0005 S_cls a dv_S_a) (TEnvFresh.consFresh (nb059_alpha_dummy_002 R S_cls) (nb059_alpha_dummy_004 R S_cls a) (nb059_wpp_notmem_0006 R S_cls) (nb059_wpp_notmem_0007 R S_cls a dv_S_a) (TEnvFresh.consFresh (nb059_alpha_dummy_001 R S_cls) (nb059_alpha_dummy_003 R S_cls a) (nb059_wpp_notmem_0008 R S_cls) (nb059_wpp_notmem_0009 R S_cls a dv_S_a) (TEnvFresh.nil (S_cls).fv))))

noncomputable def nb059_wpp_refl_0001 (R : Class) (S_cls : Class) (a : Var) (dv_S_a : a ∉ S_cls.fv) : TReflOn [((nb059_alpha_dummy_000 R S_cls), a), ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)), ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))] (S_cls).fv :=
  TEnvFresh.reflOn (nb059_compact_envfresh_0001 R S_cls a dv_S_a)

theorem nb059_compact_fv_empty_0000 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_033 R S_cls) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0010 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_033 R S_cls) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_033, fv_syn_c1c] using (nb059_compact_fv_empty_0000 R S_cls)

theorem nb059_compact_fv_empty_0001 (R : Class) (a : Var) : (nb059_alpha_dummy_036 R a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0011 (R : Class) (a : Var) : (nb059_alpha_dummy_036 R a) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_036, fv_syn_c1c] using (nb059_compact_fv_empty_0001 R a)

theorem nb059_compact_fv_empty_0002 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_032 R S_cls) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0012 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_032 R S_cls) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_032, fv_syn_c1c] using (nb059_compact_fv_empty_0002 R S_cls)

theorem nb059_compact_fv_empty_0003 (R : Class) (a : Var) : (nb059_alpha_dummy_035 R a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0013 (R : Class) (a : Var) : (nb059_alpha_dummy_035 R a) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_035, fv_syn_c1c] using (nb059_compact_fv_empty_0003 R a)

theorem nb059_compact_fv_empty_0004 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_031 R S_cls) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0014 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_031 R S_cls) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_031, fv_syn_c1c] using (nb059_compact_fv_empty_0004 R S_cls)

theorem nb059_compact_fv_empty_0005 (R : Class) (a : Var) : (nb059_alpha_dummy_034 R a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0015 (R : Class) (a : Var) : (nb059_alpha_dummy_034 R a) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_034, fv_syn_c1c] using (nb059_compact_fv_empty_0005 R a)

theorem nb059_compact_fv_empty_0006 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_029 R S_cls) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0016 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_029 R S_cls) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_029, fv_syn_c1c] using (nb059_compact_fv_empty_0006 R S_cls)

theorem nb059_compact_fv_empty_0007 (R : Class) (a : Var) : (nb059_alpha_dummy_030 R a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0017 (R : Class) (a : Var) : (nb059_alpha_dummy_030 R a) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_030, fv_syn_c1c] using (nb059_compact_fv_empty_0007 R a)

theorem nb059_compact_fv_empty_0008 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_025 R S_cls) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0018 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_025 R S_cls) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_025, fv_syn_c1c] using (nb059_compact_fv_empty_0008 R S_cls)

theorem nb059_compact_fv_empty_0009 (R : Class) (a : Var) : (nb059_alpha_dummy_027 R a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0019 (R : Class) (a : Var) : (nb059_alpha_dummy_027 R a) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_027, fv_syn_c1c] using (nb059_compact_fv_empty_0009 R a)

theorem nb059_compact_fv_empty_0010 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_026 R S_cls) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0020 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_026 R S_cls) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_026, fv_syn_c1c] using (nb059_compact_fv_empty_0010 R S_cls)

theorem nb059_compact_fv_empty_0011 (R : Class) (a : Var) : (nb059_alpha_dummy_028 R a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0021 (R : Class) (a : Var) : (nb059_alpha_dummy_028 R a) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_028, fv_syn_c1c] using (nb059_compact_fv_empty_0011 R a)

theorem nb059_compact_fv_empty_0012 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_018 R S_cls) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0022 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_018 R S_cls) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_018, fv_syn_c1c] using (nb059_compact_fv_empty_0012 R S_cls)

theorem nb059_compact_fv_empty_0013 (R : Class) (a : Var) : (nb059_alpha_dummy_020 R a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0023 (R : Class) (a : Var) : (nb059_alpha_dummy_020 R a) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_020, fv_syn_c1c] using (nb059_compact_fv_empty_0013 R a)

theorem nb059_compact_fv_empty_0014 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_017 R S_cls) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0024 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_017 R S_cls) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_017, fv_syn_c1c] using (nb059_compact_fv_empty_0014 R S_cls)

theorem nb059_compact_fv_empty_0015 (R : Class) (a : Var) : (nb059_alpha_dummy_019 R a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0025 (R : Class) (a : Var) : (nb059_alpha_dummy_019 R a) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_019, fv_syn_c1c] using (nb059_compact_fv_empty_0015 R a)

theorem nb059_compact_fv_empty_0016 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_023 R S_cls) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0026 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_023 R S_cls) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_023, fv_syn_c1c] using (nb059_compact_fv_empty_0016 R S_cls)

theorem nb059_compact_fv_empty_0017 (R : Class) (a : Var) : (nb059_alpha_dummy_024 R a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0027 (R : Class) (a : Var) : (nb059_alpha_dummy_024 R a) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_024, fv_syn_c1c] using (nb059_compact_fv_empty_0017 R a)

theorem nb059_compact_fv_empty_0018 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_021 R S_cls) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0028 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_021 R S_cls) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_021, fv_syn_c1c] using (nb059_compact_fv_empty_0018 R S_cls)

theorem nb059_compact_fv_empty_0019 (R : Class) (a : Var) : (nb059_alpha_dummy_022 R a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0029 (R : Class) (a : Var) : (nb059_alpha_dummy_022 R a) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_022, fv_syn_c1c] using (nb059_compact_fv_empty_0019 R a)

theorem nb059_compact_fv_empty_0020 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_014 R S_cls) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0030 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_014 R S_cls) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_014, fv_syn_c1c] using (nb059_compact_fv_empty_0020 R S_cls)

theorem nb059_compact_fv_empty_0021 (R : Class) (a : Var) : (nb059_alpha_dummy_016 R a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0031 (R : Class) (a : Var) : (nb059_alpha_dummy_016 R a) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_016, fv_syn_c1c] using (nb059_compact_fv_empty_0021 R a)

theorem nb059_compact_fv_empty_0022 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_013 R S_cls) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0032 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_013 R S_cls) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_013, fv_syn_c1c] using (nb059_compact_fv_empty_0022 R S_cls)

theorem nb059_compact_fv_empty_0023 (R : Class) (a : Var) : (nb059_alpha_dummy_015 R a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0033 (R : Class) (a : Var) : (nb059_alpha_dummy_015 R a) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_015, fv_syn_c1c] using (nb059_compact_fv_empty_0023 R a)

theorem nb059_compact_fv_empty_0024 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_011 R S_cls) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0034 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_011 R S_cls) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_011, fv_syn_c1c] using (nb059_compact_fv_empty_0024 R S_cls)

theorem nb059_compact_fv_empty_0025 (R : Class) (a : Var) : (nb059_alpha_dummy_012 R a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0035 (R : Class) (a : Var) : (nb059_alpha_dummy_012 R a) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_012, fv_syn_c1c] using (nb059_compact_fv_empty_0025 R a)

theorem nb059_compact_fv_empty_0026 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_009 R S_cls) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0036 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_009 R S_cls) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_009, fv_syn_c1c] using (nb059_compact_fv_empty_0026 R S_cls)

theorem nb059_compact_fv_empty_0027 (R : Class) (a : Var) : (nb059_alpha_dummy_010 R a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0037 (R : Class) (a : Var) : (nb059_alpha_dummy_010 R a) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_010, fv_syn_c1c] using (nb059_compact_fv_empty_0027 R a)

theorem nb059_compact_fv_empty_0028 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_000 R S_cls) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0038 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_000 R S_cls) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_000, fv_syn_c1c] using (nb059_compact_fv_empty_0028 R S_cls)

theorem nb059_compact_fv_empty_0029 (a : Var) : a ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0039 (a : Var) : a ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb059_compact_fv_empty_0029 a)

theorem nb059_compact_fv_empty_0030 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_002 R S_cls) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0040 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_002 R S_cls) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_002, fv_syn_c1c] using (nb059_compact_fv_empty_0030 R S_cls)

theorem nb059_compact_fv_empty_0031 (R : Class) (S_cls : Class) (a : Var) : (nb059_alpha_dummy_004 R S_cls a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0041 (R : Class) (S_cls : Class) (a : Var) : (nb059_alpha_dummy_004 R S_cls a) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_004, fv_syn_c1c] using (nb059_compact_fv_empty_0031 R S_cls a)

theorem nb059_compact_fv_empty_0032 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_001 R S_cls) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0042 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_001 R S_cls) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_001, fv_syn_c1c] using (nb059_compact_fv_empty_0032 R S_cls)

theorem nb059_compact_fv_empty_0033 (R : Class) (S_cls : Class) (a : Var) : (nb059_alpha_dummy_003 R S_cls a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb059_wpp_notmem_0043 (R : Class) (S_cls : Class) (a : Var) : (nb059_alpha_dummy_003 R S_cls a) ∉ ((syn_c1c)).fv := by
  simpa only [nb059_alpha_dummy_003, fv_syn_c1c] using (nb059_compact_fv_empty_0033 R S_cls a)

theorem nb059_compact_envfresh_0002 (R : Class) (S_cls : Class) (a : Var) : TEnvFresh [((nb059_alpha_dummy_033 R S_cls), (nb059_alpha_dummy_036 R a)), ((nb059_alpha_dummy_032 R S_cls), (nb059_alpha_dummy_035 R a)), ((nb059_alpha_dummy_031 R S_cls), (nb059_alpha_dummy_034 R a)), ((nb059_alpha_dummy_029 R S_cls), (nb059_alpha_dummy_030 R a)), ((nb059_alpha_dummy_025 R S_cls), (nb059_alpha_dummy_027 R a)), ((nb059_alpha_dummy_026 R S_cls), (nb059_alpha_dummy_028 R a)), ((nb059_alpha_dummy_018 R S_cls), (nb059_alpha_dummy_020 R a)), ((nb059_alpha_dummy_017 R S_cls), (nb059_alpha_dummy_019 R a)), ((nb059_alpha_dummy_023 R S_cls), (nb059_alpha_dummy_024 R a)), ((nb059_alpha_dummy_021 R S_cls), (nb059_alpha_dummy_022 R a)), ((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)), ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)), ((nb059_alpha_dummy_011 R S_cls), (nb059_alpha_dummy_012 R a)), ((nb059_alpha_dummy_009 R S_cls), (nb059_alpha_dummy_010 R a)), ((nb059_alpha_dummy_000 R S_cls), a), ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)), ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb059_alpha_dummy_033 R S_cls) (nb059_alpha_dummy_036 R a) (nb059_wpp_notmem_0010 R S_cls) (nb059_wpp_notmem_0011 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_032 R S_cls) (nb059_alpha_dummy_035 R a) (nb059_wpp_notmem_0012 R S_cls) (nb059_wpp_notmem_0013 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_031 R S_cls) (nb059_alpha_dummy_034 R a) (nb059_wpp_notmem_0014 R S_cls) (nb059_wpp_notmem_0015 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_029 R S_cls) (nb059_alpha_dummy_030 R a) (nb059_wpp_notmem_0016 R S_cls) (nb059_wpp_notmem_0017 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_025 R S_cls) (nb059_alpha_dummy_027 R a) (nb059_wpp_notmem_0018 R S_cls) (nb059_wpp_notmem_0019 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_026 R S_cls) (nb059_alpha_dummy_028 R a) (nb059_wpp_notmem_0020 R S_cls) (nb059_wpp_notmem_0021 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_018 R S_cls) (nb059_alpha_dummy_020 R a) (nb059_wpp_notmem_0022 R S_cls) (nb059_wpp_notmem_0023 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_017 R S_cls) (nb059_alpha_dummy_019 R a) (nb059_wpp_notmem_0024 R S_cls) (nb059_wpp_notmem_0025 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_023 R S_cls) (nb059_alpha_dummy_024 R a) (nb059_wpp_notmem_0026 R S_cls) (nb059_wpp_notmem_0027 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_021 R S_cls) (nb059_alpha_dummy_022 R a) (nb059_wpp_notmem_0028 R S_cls) (nb059_wpp_notmem_0029 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_014 R S_cls) (nb059_alpha_dummy_016 R a) (nb059_wpp_notmem_0030 R S_cls) (nb059_wpp_notmem_0031 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_013 R S_cls) (nb059_alpha_dummy_015 R a) (nb059_wpp_notmem_0032 R S_cls) (nb059_wpp_notmem_0033 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_011 R S_cls) (nb059_alpha_dummy_012 R a) (nb059_wpp_notmem_0034 R S_cls) (nb059_wpp_notmem_0035 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_009 R S_cls) (nb059_alpha_dummy_010 R a) (nb059_wpp_notmem_0036 R S_cls) (nb059_wpp_notmem_0037 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_000 R S_cls) a (nb059_wpp_notmem_0038 R S_cls) (nb059_wpp_notmem_0039 a) (TEnvFresh.consFresh (nb059_alpha_dummy_002 R S_cls) (nb059_alpha_dummy_004 R S_cls a) (nb059_wpp_notmem_0040 R S_cls) (nb059_wpp_notmem_0041 R S_cls a) (TEnvFresh.consFresh (nb059_alpha_dummy_001 R S_cls) (nb059_alpha_dummy_003 R S_cls a) (nb059_wpp_notmem_0042 R S_cls) (nb059_wpp_notmem_0043 R S_cls a) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))

noncomputable def nb059_wpp_refl_0002 (R : Class) (S_cls : Class) (a : Var) : TReflOn [((nb059_alpha_dummy_033 R S_cls), (nb059_alpha_dummy_036 R a)), ((nb059_alpha_dummy_032 R S_cls), (nb059_alpha_dummy_035 R a)), ((nb059_alpha_dummy_031 R S_cls), (nb059_alpha_dummy_034 R a)), ((nb059_alpha_dummy_029 R S_cls), (nb059_alpha_dummy_030 R a)), ((nb059_alpha_dummy_025 R S_cls), (nb059_alpha_dummy_027 R a)), ((nb059_alpha_dummy_026 R S_cls), (nb059_alpha_dummy_028 R a)), ((nb059_alpha_dummy_018 R S_cls), (nb059_alpha_dummy_020 R a)), ((nb059_alpha_dummy_017 R S_cls), (nb059_alpha_dummy_019 R a)), ((nb059_alpha_dummy_023 R S_cls), (nb059_alpha_dummy_024 R a)), ((nb059_alpha_dummy_021 R S_cls), (nb059_alpha_dummy_022 R a)), ((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)), ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)), ((nb059_alpha_dummy_011 R S_cls), (nb059_alpha_dummy_012 R a)), ((nb059_alpha_dummy_009 R S_cls), (nb059_alpha_dummy_010 R a)), ((nb059_alpha_dummy_000 R S_cls), a), ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)), ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb059_compact_envfresh_0002 R S_cls a)

theorem nb059_wpp_notmem_0044 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_033 R S_cls) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_033, fv_syn_c0] using (nb059_compact_fv_empty_0000 R S_cls)

theorem nb059_wpp_notmem_0045 (R : Class) (a : Var) : (nb059_alpha_dummy_036 R a) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_036, fv_syn_c0] using (nb059_compact_fv_empty_0001 R a)

theorem nb059_wpp_notmem_0046 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_032 R S_cls) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_032, fv_syn_c0] using (nb059_compact_fv_empty_0002 R S_cls)

theorem nb059_wpp_notmem_0047 (R : Class) (a : Var) : (nb059_alpha_dummy_035 R a) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_035, fv_syn_c0] using (nb059_compact_fv_empty_0003 R a)

theorem nb059_wpp_notmem_0048 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_031 R S_cls) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_031, fv_syn_c0] using (nb059_compact_fv_empty_0004 R S_cls)

theorem nb059_wpp_notmem_0049 (R : Class) (a : Var) : (nb059_alpha_dummy_034 R a) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_034, fv_syn_c0] using (nb059_compact_fv_empty_0005 R a)

theorem nb059_wpp_notmem_0050 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_029 R S_cls) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_029, fv_syn_c0] using (nb059_compact_fv_empty_0006 R S_cls)

theorem nb059_wpp_notmem_0051 (R : Class) (a : Var) : (nb059_alpha_dummy_030 R a) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_030, fv_syn_c0] using (nb059_compact_fv_empty_0007 R a)

theorem nb059_wpp_notmem_0052 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_025 R S_cls) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_025, fv_syn_c0] using (nb059_compact_fv_empty_0008 R S_cls)

theorem nb059_wpp_notmem_0053 (R : Class) (a : Var) : (nb059_alpha_dummy_027 R a) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_027, fv_syn_c0] using (nb059_compact_fv_empty_0009 R a)

theorem nb059_wpp_notmem_0054 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_026 R S_cls) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_026, fv_syn_c0] using (nb059_compact_fv_empty_0010 R S_cls)

theorem nb059_wpp_notmem_0055 (R : Class) (a : Var) : (nb059_alpha_dummy_028 R a) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_028, fv_syn_c0] using (nb059_compact_fv_empty_0011 R a)

theorem nb059_wpp_notmem_0056 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_018 R S_cls) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_018, fv_syn_c0] using (nb059_compact_fv_empty_0012 R S_cls)

theorem nb059_wpp_notmem_0057 (R : Class) (a : Var) : (nb059_alpha_dummy_020 R a) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_020, fv_syn_c0] using (nb059_compact_fv_empty_0013 R a)

theorem nb059_wpp_notmem_0058 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_017 R S_cls) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_017, fv_syn_c0] using (nb059_compact_fv_empty_0014 R S_cls)

theorem nb059_wpp_notmem_0059 (R : Class) (a : Var) : (nb059_alpha_dummy_019 R a) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_019, fv_syn_c0] using (nb059_compact_fv_empty_0015 R a)

theorem nb059_wpp_notmem_0060 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_023 R S_cls) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_023, fv_syn_c0] using (nb059_compact_fv_empty_0016 R S_cls)

theorem nb059_wpp_notmem_0061 (R : Class) (a : Var) : (nb059_alpha_dummy_024 R a) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_024, fv_syn_c0] using (nb059_compact_fv_empty_0017 R a)

theorem nb059_wpp_notmem_0062 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_021 R S_cls) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_021, fv_syn_c0] using (nb059_compact_fv_empty_0018 R S_cls)

theorem nb059_wpp_notmem_0063 (R : Class) (a : Var) : (nb059_alpha_dummy_022 R a) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_022, fv_syn_c0] using (nb059_compact_fv_empty_0019 R a)

theorem nb059_wpp_notmem_0064 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_014 R S_cls) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_014, fv_syn_c0] using (nb059_compact_fv_empty_0020 R S_cls)

theorem nb059_wpp_notmem_0065 (R : Class) (a : Var) : (nb059_alpha_dummy_016 R a) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_016, fv_syn_c0] using (nb059_compact_fv_empty_0021 R a)

theorem nb059_wpp_notmem_0066 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_013 R S_cls) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_013, fv_syn_c0] using (nb059_compact_fv_empty_0022 R S_cls)

theorem nb059_wpp_notmem_0067 (R : Class) (a : Var) : (nb059_alpha_dummy_015 R a) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_015, fv_syn_c0] using (nb059_compact_fv_empty_0023 R a)

theorem nb059_wpp_notmem_0068 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_011 R S_cls) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_011, fv_syn_c0] using (nb059_compact_fv_empty_0024 R S_cls)

theorem nb059_wpp_notmem_0069 (R : Class) (a : Var) : (nb059_alpha_dummy_012 R a) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_012, fv_syn_c0] using (nb059_compact_fv_empty_0025 R a)

theorem nb059_wpp_notmem_0070 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_009 R S_cls) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_009, fv_syn_c0] using (nb059_compact_fv_empty_0026 R S_cls)

theorem nb059_wpp_notmem_0071 (R : Class) (a : Var) : (nb059_alpha_dummy_010 R a) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_010, fv_syn_c0] using (nb059_compact_fv_empty_0027 R a)

theorem nb059_wpp_notmem_0072 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_000 R S_cls) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_000, fv_syn_c0] using (nb059_compact_fv_empty_0028 R S_cls)

theorem nb059_wpp_notmem_0073 (a : Var) : a ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb059_compact_fv_empty_0029 a)

theorem nb059_wpp_notmem_0074 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_002 R S_cls) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_002, fv_syn_c0] using (nb059_compact_fv_empty_0030 R S_cls)

theorem nb059_wpp_notmem_0075 (R : Class) (S_cls : Class) (a : Var) : (nb059_alpha_dummy_004 R S_cls a) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_004, fv_syn_c0] using (nb059_compact_fv_empty_0031 R S_cls a)

theorem nb059_wpp_notmem_0076 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_001 R S_cls) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_001, fv_syn_c0] using (nb059_compact_fv_empty_0032 R S_cls)

theorem nb059_wpp_notmem_0077 (R : Class) (S_cls : Class) (a : Var) : (nb059_alpha_dummy_003 R S_cls a) ∉ ((syn_c0)).fv := by
  simpa only [nb059_alpha_dummy_003, fv_syn_c0] using (nb059_compact_fv_empty_0033 R S_cls a)

theorem nb059_compact_envfresh_0003 (R : Class) (S_cls : Class) (a : Var) : TEnvFresh [((nb059_alpha_dummy_033 R S_cls), (nb059_alpha_dummy_036 R a)), ((nb059_alpha_dummy_032 R S_cls), (nb059_alpha_dummy_035 R a)), ((nb059_alpha_dummy_031 R S_cls), (nb059_alpha_dummy_034 R a)), ((nb059_alpha_dummy_029 R S_cls), (nb059_alpha_dummy_030 R a)), ((nb059_alpha_dummy_025 R S_cls), (nb059_alpha_dummy_027 R a)), ((nb059_alpha_dummy_026 R S_cls), (nb059_alpha_dummy_028 R a)), ((nb059_alpha_dummy_018 R S_cls), (nb059_alpha_dummy_020 R a)), ((nb059_alpha_dummy_017 R S_cls), (nb059_alpha_dummy_019 R a)), ((nb059_alpha_dummy_023 R S_cls), (nb059_alpha_dummy_024 R a)), ((nb059_alpha_dummy_021 R S_cls), (nb059_alpha_dummy_022 R a)), ((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)), ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)), ((nb059_alpha_dummy_011 R S_cls), (nb059_alpha_dummy_012 R a)), ((nb059_alpha_dummy_009 R S_cls), (nb059_alpha_dummy_010 R a)), ((nb059_alpha_dummy_000 R S_cls), a), ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)), ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb059_alpha_dummy_033 R S_cls) (nb059_alpha_dummy_036 R a) (nb059_wpp_notmem_0044 R S_cls) (nb059_wpp_notmem_0045 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_032 R S_cls) (nb059_alpha_dummy_035 R a) (nb059_wpp_notmem_0046 R S_cls) (nb059_wpp_notmem_0047 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_031 R S_cls) (nb059_alpha_dummy_034 R a) (nb059_wpp_notmem_0048 R S_cls) (nb059_wpp_notmem_0049 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_029 R S_cls) (nb059_alpha_dummy_030 R a) (nb059_wpp_notmem_0050 R S_cls) (nb059_wpp_notmem_0051 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_025 R S_cls) (nb059_alpha_dummy_027 R a) (nb059_wpp_notmem_0052 R S_cls) (nb059_wpp_notmem_0053 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_026 R S_cls) (nb059_alpha_dummy_028 R a) (nb059_wpp_notmem_0054 R S_cls) (nb059_wpp_notmem_0055 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_018 R S_cls) (nb059_alpha_dummy_020 R a) (nb059_wpp_notmem_0056 R S_cls) (nb059_wpp_notmem_0057 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_017 R S_cls) (nb059_alpha_dummy_019 R a) (nb059_wpp_notmem_0058 R S_cls) (nb059_wpp_notmem_0059 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_023 R S_cls) (nb059_alpha_dummy_024 R a) (nb059_wpp_notmem_0060 R S_cls) (nb059_wpp_notmem_0061 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_021 R S_cls) (nb059_alpha_dummy_022 R a) (nb059_wpp_notmem_0062 R S_cls) (nb059_wpp_notmem_0063 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_014 R S_cls) (nb059_alpha_dummy_016 R a) (nb059_wpp_notmem_0064 R S_cls) (nb059_wpp_notmem_0065 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_013 R S_cls) (nb059_alpha_dummy_015 R a) (nb059_wpp_notmem_0066 R S_cls) (nb059_wpp_notmem_0067 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_011 R S_cls) (nb059_alpha_dummy_012 R a) (nb059_wpp_notmem_0068 R S_cls) (nb059_wpp_notmem_0069 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_009 R S_cls) (nb059_alpha_dummy_010 R a) (nb059_wpp_notmem_0070 R S_cls) (nb059_wpp_notmem_0071 R a) (TEnvFresh.consFresh (nb059_alpha_dummy_000 R S_cls) a (nb059_wpp_notmem_0072 R S_cls) (nb059_wpp_notmem_0073 a) (TEnvFresh.consFresh (nb059_alpha_dummy_002 R S_cls) (nb059_alpha_dummy_004 R S_cls a) (nb059_wpp_notmem_0074 R S_cls) (nb059_wpp_notmem_0075 R S_cls a) (TEnvFresh.consFresh (nb059_alpha_dummy_001 R S_cls) (nb059_alpha_dummy_003 R S_cls a) (nb059_wpp_notmem_0076 R S_cls) (nb059_wpp_notmem_0077 R S_cls a) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))

noncomputable def nb059_wpp_refl_0003 (R : Class) (S_cls : Class) (a : Var) : TReflOn [((nb059_alpha_dummy_033 R S_cls), (nb059_alpha_dummy_036 R a)), ((nb059_alpha_dummy_032 R S_cls), (nb059_alpha_dummy_035 R a)), ((nb059_alpha_dummy_031 R S_cls), (nb059_alpha_dummy_034 R a)), ((nb059_alpha_dummy_029 R S_cls), (nb059_alpha_dummy_030 R a)), ((nb059_alpha_dummy_025 R S_cls), (nb059_alpha_dummy_027 R a)), ((nb059_alpha_dummy_026 R S_cls), (nb059_alpha_dummy_028 R a)), ((nb059_alpha_dummy_018 R S_cls), (nb059_alpha_dummy_020 R a)), ((nb059_alpha_dummy_017 R S_cls), (nb059_alpha_dummy_019 R a)), ((nb059_alpha_dummy_023 R S_cls), (nb059_alpha_dummy_024 R a)), ((nb059_alpha_dummy_021 R S_cls), (nb059_alpha_dummy_022 R a)), ((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)), ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)), ((nb059_alpha_dummy_011 R S_cls), (nb059_alpha_dummy_012 R a)), ((nb059_alpha_dummy_009 R S_cls), (nb059_alpha_dummy_010 R a)), ((nb059_alpha_dummy_000 R S_cls), a), ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)), ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb059_compact_envfresh_0003 R S_cls a)

noncomputable def nb059_split_alpha_0000 (R : Class) (S_cls : Class) (a : Var) : TAlphaWff [((nb059_alpha_dummy_033 R S_cls), (nb059_alpha_dummy_036 R a)), ((nb059_alpha_dummy_032 R S_cls), (nb059_alpha_dummy_035 R a)), ((nb059_alpha_dummy_031 R S_cls), (nb059_alpha_dummy_034 R a)), ((nb059_alpha_dummy_029 R S_cls), (nb059_alpha_dummy_030 R a)), ((nb059_alpha_dummy_025 R S_cls), (nb059_alpha_dummy_027 R a)), ((nb059_alpha_dummy_026 R S_cls), (nb059_alpha_dummy_028 R a)), ((nb059_alpha_dummy_018 R S_cls), (nb059_alpha_dummy_020 R a)), ((nb059_alpha_dummy_017 R S_cls), (nb059_alpha_dummy_019 R a)), ((nb059_alpha_dummy_023 R S_cls), (nb059_alpha_dummy_024 R a)), ((nb059_alpha_dummy_021 R S_cls), (nb059_alpha_dummy_022 R a)), ((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)), ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)), ((nb059_alpha_dummy_011 R S_cls), (nb059_alpha_dummy_012 R a)), ((nb059_alpha_dummy_009 R S_cls), (nb059_alpha_dummy_010 R a)), ((nb059_alpha_dummy_000 R S_cls), a), ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)), ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb059_alpha_dummy_032 R S_cls)) (Class.cv (nb059_alpha_dummy_033 R S_cls))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb059_alpha_dummy_031 R S_cls)) (syn_cun (Class.cv (nb059_alpha_dummy_032 R S_cls)) (Class.cv (nb059_alpha_dummy_033 R S_cls)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb059_alpha_dummy_035 R a)) (Class.cv (nb059_alpha_dummy_036 R a))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb059_alpha_dummy_034 R a)) (syn_cun (Class.cv (nb059_alpha_dummy_035 R a)) (Class.cv (nb059_alpha_dummy_036 R a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0024 R S_cls) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0025 R a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0022 R S_cls) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0023 R a) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0028 R S_cls) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0029 R a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0026 R S_cls) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0027 R a) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0024 R S_cls) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0025 R a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0022 R S_cls) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0023 R a) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0028 R S_cls) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0029 R a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0026 R S_cls) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0027 R a) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb059_alpha_dummy_033 R S_cls), (nb059_alpha_dummy_036 R a)), ((nb059_alpha_dummy_032 R S_cls), (nb059_alpha_dummy_035 R a)), ((nb059_alpha_dummy_031 R S_cls), (nb059_alpha_dummy_034 R a)), ((nb059_alpha_dummy_029 R S_cls), (nb059_alpha_dummy_030 R a)), ((nb059_alpha_dummy_025 R S_cls), (nb059_alpha_dummy_027 R a)), ((nb059_alpha_dummy_026 R S_cls), (nb059_alpha_dummy_028 R a)), ((nb059_alpha_dummy_018 R S_cls), (nb059_alpha_dummy_020 R a)), ((nb059_alpha_dummy_017 R S_cls), (nb059_alpha_dummy_019 R a)), ((nb059_alpha_dummy_023 R S_cls), (nb059_alpha_dummy_024 R a)), ((nb059_alpha_dummy_021 R S_cls), (nb059_alpha_dummy_022 R a)), ((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)), ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)), ((nb059_alpha_dummy_011 R S_cls), (nb059_alpha_dummy_012 R a)), ((nb059_alpha_dummy_009 R S_cls), (nb059_alpha_dummy_010 R a)), ((nb059_alpha_dummy_000 R S_cls), a), ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)), ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))] (syn_c0) (nb059_wpp_refl_0003 R S_cls a))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0032 R S_cls) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0033 R a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0030 R S_cls) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0031 R a) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0032 R S_cls) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0033 R a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0030 R S_cls) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0031 R a) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0036 R S_cls) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0037 R a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0034 R S_cls) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0035 R a) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0036 R S_cls) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0037 R a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0034 R S_cls) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0035 R a) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb059_wpp_notmem_0078 (R : Class) (S_cls : Class) : (nb059_alpha_dummy_029 R S_cls) ∉ ((syn_cnnc)).fv := by
  simpa only [nb059_alpha_dummy_029, fv_syn_cnnc] using (nb059_compact_fv_empty_0006 R S_cls)

theorem nb059_wpp_notmem_0079 (R : Class) (a : Var) : (nb059_alpha_dummy_030 R a) ∉ ((syn_cnnc)).fv := by
  simpa only [nb059_alpha_dummy_030, fv_syn_cnnc] using (nb059_compact_fv_empty_0007 R a)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
