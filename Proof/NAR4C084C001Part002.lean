import NAR4C084C001Part001

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

theorem nb084_support_mem_0045 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_012 x y A R) ∈ (((syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))).fv ∪ ((syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb084_focused_notmem_0000 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_000 A B R) ∉ A.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb084_compact_envfresh_0000 (A : Class) (B : Class) (R : Class) (d : Var) (dv_A_d : d ∉ A.fv) : TEnvFresh [((nb084_alpha_dummy_000 A B R), d)] A.fv := by
  exact (TEnvFresh.consFresh (nb084_alpha_dummy_000 A B R) d (nb084_focused_notmem_0000 A B R) dv_A_d (TEnvFresh.nil A.fv))

noncomputable def nb084_focused_refl_0000 (A : Class) (B : Class) (R : Class) (d : Var) (dv_A_d : d ∉ A.fv) : TReflOn [((nb084_alpha_dummy_000 A B R), d)] A.fv :=
  TEnvFresh.reflOn (nb084_compact_envfresh_0000 A B R d dv_A_d)

theorem nb084_focused_notmem_0001 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_001 A B R) ∉ B.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 1 ∉ B.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun u hu => Finset.mem_union_right _ (hu))

theorem nb084_focused_notmem_0002 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_000 A B R) ∉ B.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0 ∉ B.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_right _ (hu))

theorem nb084_compact_envfresh_0001 (x : Var) (A : Class) (B : Class) (R : Class) (d : Var) (dv_B_d : d ∉ B.fv) (dv_B_x : x ∉ B.fv) : TEnvFresh [((nb084_alpha_dummy_001 A B R), x), ((nb084_alpha_dummy_000 A B R), d)] B.fv := by
  exact (TEnvFresh.consFresh (nb084_alpha_dummy_001 A B R) x (nb084_focused_notmem_0001 A B R) dv_B_x (TEnvFresh.consFresh (nb084_alpha_dummy_000 A B R) d (nb084_focused_notmem_0002 A B R) dv_B_d (TEnvFresh.nil B.fv)))

noncomputable def nb084_focused_refl_0001 (x : Var) (A : Class) (B : Class) (R : Class) (d : Var) (dv_B_d : d ∉ B.fv) (dv_B_x : x ∉ B.fv) : TReflOn [((nb084_alpha_dummy_001 A B R), x), ((nb084_alpha_dummy_000 A B R), d)] B.fv :=
  TEnvFresh.reflOn (nb084_compact_envfresh_0001 x A B R d dv_B_d dv_B_x)

theorem nb084_focused_notmem_0003 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_002 A B R) ∉ B.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 2 ∉ B.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 2 (fun u hu => Finset.mem_union_right _ (hu))

theorem nb084_compact_envfresh_0002 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (d : Var) (dv_B_d : d ∉ B.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) : TEnvFresh [((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x), ((nb084_alpha_dummy_000 A B R), d)] B.fv := by
  exact (TEnvFresh.consFresh (nb084_alpha_dummy_002 A B R) y (nb084_focused_notmem_0003 A B R) dv_B_y (TEnvFresh.consFresh (nb084_alpha_dummy_001 A B R) x (nb084_focused_notmem_0001 A B R) dv_B_x (TEnvFresh.consFresh (nb084_alpha_dummy_000 A B R) d (nb084_focused_notmem_0002 A B R) dv_B_d (TEnvFresh.nil B.fv))))

noncomputable def nb084_focused_refl_0002 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (d : Var) (dv_B_d : d ∉ B.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) : TReflOn [((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x), ((nb084_alpha_dummy_000 A B R), d)] B.fv :=
  TEnvFresh.reflOn (nb084_compact_envfresh_0002 x y A B R d dv_B_d dv_B_x dv_B_y)

theorem nb084_focused_notmem_0004 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_003 A B R) ∉ A.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084_alpha_dummy_001 A B R))).fv ∪ ((Class.cv (nb084_alpha_dummy_002 A B R))).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb084_focused_notmem_0005 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_005 x y A R) ∉ A.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb084_focused_notmem_0006 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_002 A B R) ∉ A.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 2 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 2 (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb084_focused_notmem_0007 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_001 A B R) ∉ A.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 1 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb084_compact_envfresh_0003 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (d : Var) (dv_A_d : d ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) : TEnvFresh [((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)), ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x), ((nb084_alpha_dummy_000 A B R), d)] A.fv := by
  exact (TEnvFresh.consFresh (nb084_alpha_dummy_003 A B R) (nb084_alpha_dummy_005 x y A R) (nb084_focused_notmem_0004 A B R) (nb084_focused_notmem_0005 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_002 A B R) y (nb084_focused_notmem_0006 A B R) dv_A_y (TEnvFresh.consFresh (nb084_alpha_dummy_001 A B R) x (nb084_focused_notmem_0007 A B R) dv_A_x (TEnvFresh.consFresh (nb084_alpha_dummy_000 A B R) d (nb084_focused_notmem_0000 A B R) dv_A_d (TEnvFresh.nil A.fv)))))

noncomputable def nb084_focused_refl_0003 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (d : Var) (dv_A_d : d ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) : TReflOn [((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)), ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x), ((nb084_alpha_dummy_000 A B R), d)] A.fv :=
  TEnvFresh.reflOn (nb084_compact_envfresh_0003 x y A B R d dv_A_d dv_A_x dv_A_y)

theorem nb084_focused_notmem_0008 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_004 A B R) ∉ A.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084_alpha_dummy_001 A B R))).fv ∪ ((Class.cv (nb084_alpha_dummy_002 A B R))).fv) 1 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb084_focused_notmem_0009 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_006 x y A R) ∉ A.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb084_compact_envfresh_0004 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (d : Var) (dv_A_d : d ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) : TEnvFresh [((nb084_alpha_dummy_004 A B R), (nb084_alpha_dummy_006 x y A R)), ((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)), ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x), ((nb084_alpha_dummy_000 A B R), d)] A.fv := by
  exact (TEnvFresh.consFresh (nb084_alpha_dummy_004 A B R) (nb084_alpha_dummy_006 x y A R) (nb084_focused_notmem_0008 A B R) (nb084_focused_notmem_0009 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_003 A B R) (nb084_alpha_dummy_005 x y A R) (nb084_focused_notmem_0004 A B R) (nb084_focused_notmem_0005 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_002 A B R) y (nb084_focused_notmem_0006 A B R) dv_A_y (TEnvFresh.consFresh (nb084_alpha_dummy_001 A B R) x (nb084_focused_notmem_0007 A B R) dv_A_x (TEnvFresh.consFresh (nb084_alpha_dummy_000 A B R) d (nb084_focused_notmem_0000 A B R) dv_A_d (TEnvFresh.nil A.fv))))))

noncomputable def nb084_focused_refl_0004 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (d : Var) (dv_A_d : d ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) : TReflOn [((nb084_alpha_dummy_004 A B R), (nb084_alpha_dummy_006 x y A R)), ((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)), ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x), ((nb084_alpha_dummy_000 A B R), d)] A.fv :=
  TEnvFresh.reflOn (nb084_compact_envfresh_0004 x y A B R d dv_A_d dv_A_x dv_A_y)

theorem nb084_compact_fv_empty_0000 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_025 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0000 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_025 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_025, fv_syn_c1c] using (nb084_compact_fv_empty_0000 A B R)

theorem nb084_compact_fv_empty_0001 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_028 x y A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0001 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_028 x y A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_028, fv_syn_c1c] using (nb084_compact_fv_empty_0001 x y A R)

theorem nb084_compact_fv_empty_0002 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_024 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0002 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_024 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_024, fv_syn_c1c] using (nb084_compact_fv_empty_0002 A B R)

theorem nb084_compact_fv_empty_0003 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_027 x y A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0003 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_027 x y A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_027, fv_syn_c1c] using (nb084_compact_fv_empty_0003 x y A R)

theorem nb084_compact_fv_empty_0004 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_023 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0004 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_023 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_023, fv_syn_c1c] using (nb084_compact_fv_empty_0004 A B R)

theorem nb084_compact_fv_empty_0005 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_026 x y A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0005 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_026 x y A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_026, fv_syn_c1c] using (nb084_compact_fv_empty_0005 x y A R)

theorem nb084_compact_fv_empty_0006 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_021 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0006 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_021 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_021, fv_syn_c1c] using (nb084_compact_fv_empty_0006 A B R)

theorem nb084_compact_fv_empty_0007 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_022 x y A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0007 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_022 x y A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_022, fv_syn_c1c] using (nb084_compact_fv_empty_0007 x y A R)

theorem nb084_compact_fv_empty_0008 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_017 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0008 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_017 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_017, fv_syn_c1c] using (nb084_compact_fv_empty_0008 A B R)

theorem nb084_compact_fv_empty_0009 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_019 x y A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0009 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_019 x y A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_019, fv_syn_c1c] using (nb084_compact_fv_empty_0009 x y A R)

theorem nb084_compact_fv_empty_0010 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_018 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0010 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_018 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_018, fv_syn_c1c] using (nb084_compact_fv_empty_0010 A B R)

theorem nb084_compact_fv_empty_0011 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_020 x y A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0011 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_020 x y A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_020, fv_syn_c1c] using (nb084_compact_fv_empty_0011 x y A R)

theorem nb084_compact_fv_empty_0012 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_010 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0012 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_010 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_010, fv_syn_c1c] using (nb084_compact_fv_empty_0012 A B R)

theorem nb084_compact_fv_empty_0013 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_012 x y A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0013 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_012 x y A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_012, fv_syn_c1c] using (nb084_compact_fv_empty_0013 x y A R)

theorem nb084_compact_fv_empty_0014 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_009 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0014 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_009 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_009, fv_syn_c1c] using (nb084_compact_fv_empty_0014 A B R)

theorem nb084_compact_fv_empty_0015 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_011 x y A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0015 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_011 x y A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_011, fv_syn_c1c] using (nb084_compact_fv_empty_0015 x y A R)

theorem nb084_compact_fv_empty_0016 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_015 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0016 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_015 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_015, fv_syn_c1c] using (nb084_compact_fv_empty_0016 A B R)

theorem nb084_compact_fv_empty_0017 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_016 x y A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0017 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_016 x y A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_016, fv_syn_c1c] using (nb084_compact_fv_empty_0017 x y A R)

theorem nb084_compact_fv_empty_0018 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_013 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0018 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_013 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_013, fv_syn_c1c] using (nb084_compact_fv_empty_0018 A B R)

theorem nb084_compact_fv_empty_0019 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_014 x y A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0019 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_014 x y A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_014, fv_syn_c1c] using (nb084_compact_fv_empty_0019 x y A R)

theorem nb084_compact_fv_empty_0020 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_004 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0020 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_004 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_004, fv_syn_c1c] using (nb084_compact_fv_empty_0020 A B R)

theorem nb084_compact_fv_empty_0021 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_006 x y A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0021 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_006 x y A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_006, fv_syn_c1c] using (nb084_compact_fv_empty_0021 x y A R)

theorem nb084_compact_fv_empty_0022 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_003 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0022 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_003 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_003, fv_syn_c1c] using (nb084_compact_fv_empty_0022 A B R)

theorem nb084_compact_fv_empty_0023 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_005 x y A R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0023 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_005 x y A R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_005, fv_syn_c1c] using (nb084_compact_fv_empty_0023 x y A R)

theorem nb084_compact_fv_empty_0024 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_002 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0024 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_002 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_002, fv_syn_c1c] using (nb084_compact_fv_empty_0024 A B R)

theorem nb084_compact_fv_empty_0025 (y : Var) : y ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0025 (y : Var) : y ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb084_compact_fv_empty_0025 y)

theorem nb084_compact_fv_empty_0026 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_001 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0026 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_001 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_001, fv_syn_c1c] using (nb084_compact_fv_empty_0026 A B R)

theorem nb084_compact_fv_empty_0027 (x : Var) : x ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0027 (x : Var) : x ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb084_compact_fv_empty_0027 x)

theorem nb084_compact_fv_empty_0028 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_000 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0028 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_000 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb084_alpha_dummy_000, fv_syn_c1c] using (nb084_compact_fv_empty_0028 A B R)

theorem nb084_compact_fv_empty_0029 (d : Var) : d ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb084_wpp_notmem_0029 (d : Var) : d ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb084_compact_fv_empty_0029 d)

theorem nb084_compact_envfresh_0005 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (d : Var) : TEnvFresh [((nb084_alpha_dummy_025 A B R), (nb084_alpha_dummy_028 x y A R)), ((nb084_alpha_dummy_024 A B R), (nb084_alpha_dummy_027 x y A R)), ((nb084_alpha_dummy_023 A B R), (nb084_alpha_dummy_026 x y A R)), ((nb084_alpha_dummy_021 A B R), (nb084_alpha_dummy_022 x y A R)), ((nb084_alpha_dummy_017 A B R), (nb084_alpha_dummy_019 x y A R)), ((nb084_alpha_dummy_018 A B R), (nb084_alpha_dummy_020 x y A R)), ((nb084_alpha_dummy_010 A B R), (nb084_alpha_dummy_012 x y A R)), ((nb084_alpha_dummy_009 A B R), (nb084_alpha_dummy_011 x y A R)), ((nb084_alpha_dummy_015 A B R), (nb084_alpha_dummy_016 x y A R)), ((nb084_alpha_dummy_013 A B R), (nb084_alpha_dummy_014 x y A R)), ((nb084_alpha_dummy_004 A B R), (nb084_alpha_dummy_006 x y A R)), ((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)), ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x), ((nb084_alpha_dummy_000 A B R), d)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb084_alpha_dummy_025 A B R) (nb084_alpha_dummy_028 x y A R) (nb084_wpp_notmem_0000 A B R) (nb084_wpp_notmem_0001 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_024 A B R) (nb084_alpha_dummy_027 x y A R) (nb084_wpp_notmem_0002 A B R) (nb084_wpp_notmem_0003 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_023 A B R) (nb084_alpha_dummy_026 x y A R) (nb084_wpp_notmem_0004 A B R) (nb084_wpp_notmem_0005 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_021 A B R) (nb084_alpha_dummy_022 x y A R) (nb084_wpp_notmem_0006 A B R) (nb084_wpp_notmem_0007 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_017 A B R) (nb084_alpha_dummy_019 x y A R) (nb084_wpp_notmem_0008 A B R) (nb084_wpp_notmem_0009 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_018 A B R) (nb084_alpha_dummy_020 x y A R) (nb084_wpp_notmem_0010 A B R) (nb084_wpp_notmem_0011 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_010 A B R) (nb084_alpha_dummy_012 x y A R) (nb084_wpp_notmem_0012 A B R) (nb084_wpp_notmem_0013 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_009 A B R) (nb084_alpha_dummy_011 x y A R) (nb084_wpp_notmem_0014 A B R) (nb084_wpp_notmem_0015 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_015 A B R) (nb084_alpha_dummy_016 x y A R) (nb084_wpp_notmem_0016 A B R) (nb084_wpp_notmem_0017 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_013 A B R) (nb084_alpha_dummy_014 x y A R) (nb084_wpp_notmem_0018 A B R) (nb084_wpp_notmem_0019 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_004 A B R) (nb084_alpha_dummy_006 x y A R) (nb084_wpp_notmem_0020 A B R) (nb084_wpp_notmem_0021 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_003 A B R) (nb084_alpha_dummy_005 x y A R) (nb084_wpp_notmem_0022 A B R) (nb084_wpp_notmem_0023 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_002 A B R) y (nb084_wpp_notmem_0024 A B R) (nb084_wpp_notmem_0025 y) (TEnvFresh.consFresh (nb084_alpha_dummy_001 A B R) x (nb084_wpp_notmem_0026 A B R) (nb084_wpp_notmem_0027 x) (TEnvFresh.consFresh (nb084_alpha_dummy_000 A B R) d (nb084_wpp_notmem_0028 A B R) (nb084_wpp_notmem_0029 d) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb084_wpp_refl_0000 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (d : Var) : TReflOn [((nb084_alpha_dummy_025 A B R), (nb084_alpha_dummy_028 x y A R)), ((nb084_alpha_dummy_024 A B R), (nb084_alpha_dummy_027 x y A R)), ((nb084_alpha_dummy_023 A B R), (nb084_alpha_dummy_026 x y A R)), ((nb084_alpha_dummy_021 A B R), (nb084_alpha_dummy_022 x y A R)), ((nb084_alpha_dummy_017 A B R), (nb084_alpha_dummy_019 x y A R)), ((nb084_alpha_dummy_018 A B R), (nb084_alpha_dummy_020 x y A R)), ((nb084_alpha_dummy_010 A B R), (nb084_alpha_dummy_012 x y A R)), ((nb084_alpha_dummy_009 A B R), (nb084_alpha_dummy_011 x y A R)), ((nb084_alpha_dummy_015 A B R), (nb084_alpha_dummy_016 x y A R)), ((nb084_alpha_dummy_013 A B R), (nb084_alpha_dummy_014 x y A R)), ((nb084_alpha_dummy_004 A B R), (nb084_alpha_dummy_006 x y A R)), ((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)), ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x), ((nb084_alpha_dummy_000 A B R), d)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb084_compact_envfresh_0005 x y A B R d)

theorem nb084_wpp_notmem_0030 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_025 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_025, fv_syn_c0] using (nb084_compact_fv_empty_0000 A B R)

theorem nb084_wpp_notmem_0031 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_028 x y A R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_028, fv_syn_c0] using (nb084_compact_fv_empty_0001 x y A R)

theorem nb084_wpp_notmem_0032 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_024 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_024, fv_syn_c0] using (nb084_compact_fv_empty_0002 A B R)

theorem nb084_wpp_notmem_0033 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_027 x y A R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_027, fv_syn_c0] using (nb084_compact_fv_empty_0003 x y A R)

theorem nb084_wpp_notmem_0034 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_023 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_023, fv_syn_c0] using (nb084_compact_fv_empty_0004 A B R)

theorem nb084_wpp_notmem_0035 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_026 x y A R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_026, fv_syn_c0] using (nb084_compact_fv_empty_0005 x y A R)

theorem nb084_wpp_notmem_0036 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_021 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_021, fv_syn_c0] using (nb084_compact_fv_empty_0006 A B R)

theorem nb084_wpp_notmem_0037 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_022 x y A R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_022, fv_syn_c0] using (nb084_compact_fv_empty_0007 x y A R)

theorem nb084_wpp_notmem_0038 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_017 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_017, fv_syn_c0] using (nb084_compact_fv_empty_0008 A B R)

theorem nb084_wpp_notmem_0039 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_019 x y A R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_019, fv_syn_c0] using (nb084_compact_fv_empty_0009 x y A R)

theorem nb084_wpp_notmem_0040 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_018 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_018, fv_syn_c0] using (nb084_compact_fv_empty_0010 A B R)

theorem nb084_wpp_notmem_0041 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_020 x y A R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_020, fv_syn_c0] using (nb084_compact_fv_empty_0011 x y A R)

theorem nb084_wpp_notmem_0042 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_010 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_010, fv_syn_c0] using (nb084_compact_fv_empty_0012 A B R)

theorem nb084_wpp_notmem_0043 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_012 x y A R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_012, fv_syn_c0] using (nb084_compact_fv_empty_0013 x y A R)

theorem nb084_wpp_notmem_0044 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_009 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_009, fv_syn_c0] using (nb084_compact_fv_empty_0014 A B R)

theorem nb084_wpp_notmem_0045 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_011 x y A R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_011, fv_syn_c0] using (nb084_compact_fv_empty_0015 x y A R)

theorem nb084_wpp_notmem_0046 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_015 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_015, fv_syn_c0] using (nb084_compact_fv_empty_0016 A B R)

theorem nb084_wpp_notmem_0047 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_016 x y A R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_016, fv_syn_c0] using (nb084_compact_fv_empty_0017 x y A R)

theorem nb084_wpp_notmem_0048 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_013 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_013, fv_syn_c0] using (nb084_compact_fv_empty_0018 A B R)

theorem nb084_wpp_notmem_0049 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_014 x y A R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_014, fv_syn_c0] using (nb084_compact_fv_empty_0019 x y A R)

theorem nb084_wpp_notmem_0050 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_004 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_004, fv_syn_c0] using (nb084_compact_fv_empty_0020 A B R)

theorem nb084_wpp_notmem_0051 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_006 x y A R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_006, fv_syn_c0] using (nb084_compact_fv_empty_0021 x y A R)

theorem nb084_wpp_notmem_0052 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_003 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_003, fv_syn_c0] using (nb084_compact_fv_empty_0022 A B R)

theorem nb084_wpp_notmem_0053 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_005 x y A R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_005, fv_syn_c0] using (nb084_compact_fv_empty_0023 x y A R)

theorem nb084_wpp_notmem_0054 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_002 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_002, fv_syn_c0] using (nb084_compact_fv_empty_0024 A B R)

theorem nb084_wpp_notmem_0055 (y : Var) : y ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb084_compact_fv_empty_0025 y)

theorem nb084_wpp_notmem_0056 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_001 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_001, fv_syn_c0] using (nb084_compact_fv_empty_0026 A B R)

theorem nb084_wpp_notmem_0057 (x : Var) : x ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb084_compact_fv_empty_0027 x)

theorem nb084_wpp_notmem_0058 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_000 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb084_alpha_dummy_000, fv_syn_c0] using (nb084_compact_fv_empty_0028 A B R)

theorem nb084_wpp_notmem_0059 (d : Var) : d ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb084_compact_fv_empty_0029 d)

theorem nb084_compact_envfresh_0006 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (d : Var) : TEnvFresh [((nb084_alpha_dummy_025 A B R), (nb084_alpha_dummy_028 x y A R)), ((nb084_alpha_dummy_024 A B R), (nb084_alpha_dummy_027 x y A R)), ((nb084_alpha_dummy_023 A B R), (nb084_alpha_dummy_026 x y A R)), ((nb084_alpha_dummy_021 A B R), (nb084_alpha_dummy_022 x y A R)), ((nb084_alpha_dummy_017 A B R), (nb084_alpha_dummy_019 x y A R)), ((nb084_alpha_dummy_018 A B R), (nb084_alpha_dummy_020 x y A R)), ((nb084_alpha_dummy_010 A B R), (nb084_alpha_dummy_012 x y A R)), ((nb084_alpha_dummy_009 A B R), (nb084_alpha_dummy_011 x y A R)), ((nb084_alpha_dummy_015 A B R), (nb084_alpha_dummy_016 x y A R)), ((nb084_alpha_dummy_013 A B R), (nb084_alpha_dummy_014 x y A R)), ((nb084_alpha_dummy_004 A B R), (nb084_alpha_dummy_006 x y A R)), ((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)), ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x), ((nb084_alpha_dummy_000 A B R), d)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb084_alpha_dummy_025 A B R) (nb084_alpha_dummy_028 x y A R) (nb084_wpp_notmem_0030 A B R) (nb084_wpp_notmem_0031 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_024 A B R) (nb084_alpha_dummy_027 x y A R) (nb084_wpp_notmem_0032 A B R) (nb084_wpp_notmem_0033 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_023 A B R) (nb084_alpha_dummy_026 x y A R) (nb084_wpp_notmem_0034 A B R) (nb084_wpp_notmem_0035 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_021 A B R) (nb084_alpha_dummy_022 x y A R) (nb084_wpp_notmem_0036 A B R) (nb084_wpp_notmem_0037 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_017 A B R) (nb084_alpha_dummy_019 x y A R) (nb084_wpp_notmem_0038 A B R) (nb084_wpp_notmem_0039 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_018 A B R) (nb084_alpha_dummy_020 x y A R) (nb084_wpp_notmem_0040 A B R) (nb084_wpp_notmem_0041 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_010 A B R) (nb084_alpha_dummy_012 x y A R) (nb084_wpp_notmem_0042 A B R) (nb084_wpp_notmem_0043 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_009 A B R) (nb084_alpha_dummy_011 x y A R) (nb084_wpp_notmem_0044 A B R) (nb084_wpp_notmem_0045 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_015 A B R) (nb084_alpha_dummy_016 x y A R) (nb084_wpp_notmem_0046 A B R) (nb084_wpp_notmem_0047 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_013 A B R) (nb084_alpha_dummy_014 x y A R) (nb084_wpp_notmem_0048 A B R) (nb084_wpp_notmem_0049 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_004 A B R) (nb084_alpha_dummy_006 x y A R) (nb084_wpp_notmem_0050 A B R) (nb084_wpp_notmem_0051 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_003 A B R) (nb084_alpha_dummy_005 x y A R) (nb084_wpp_notmem_0052 A B R) (nb084_wpp_notmem_0053 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_002 A B R) y (nb084_wpp_notmem_0054 A B R) (nb084_wpp_notmem_0055 y) (TEnvFresh.consFresh (nb084_alpha_dummy_001 A B R) x (nb084_wpp_notmem_0056 A B R) (nb084_wpp_notmem_0057 x) (TEnvFresh.consFresh (nb084_alpha_dummy_000 A B R) d (nb084_wpp_notmem_0058 A B R) (nb084_wpp_notmem_0059 d) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))

noncomputable def nb084_wpp_refl_0001 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (d : Var) : TReflOn [((nb084_alpha_dummy_025 A B R), (nb084_alpha_dummy_028 x y A R)), ((nb084_alpha_dummy_024 A B R), (nb084_alpha_dummy_027 x y A R)), ((nb084_alpha_dummy_023 A B R), (nb084_alpha_dummy_026 x y A R)), ((nb084_alpha_dummy_021 A B R), (nb084_alpha_dummy_022 x y A R)), ((nb084_alpha_dummy_017 A B R), (nb084_alpha_dummy_019 x y A R)), ((nb084_alpha_dummy_018 A B R), (nb084_alpha_dummy_020 x y A R)), ((nb084_alpha_dummy_010 A B R), (nb084_alpha_dummy_012 x y A R)), ((nb084_alpha_dummy_009 A B R), (nb084_alpha_dummy_011 x y A R)), ((nb084_alpha_dummy_015 A B R), (nb084_alpha_dummy_016 x y A R)), ((nb084_alpha_dummy_013 A B R), (nb084_alpha_dummy_014 x y A R)), ((nb084_alpha_dummy_004 A B R), (nb084_alpha_dummy_006 x y A R)), ((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)), ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x), ((nb084_alpha_dummy_000 A B R), d)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb084_compact_envfresh_0006 x y A B R d)

theorem nb084_wpp_notmem_0060 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_021 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb084_alpha_dummy_021, fv_syn_cnnc] using (nb084_compact_fv_empty_0006 A B R)

theorem nb084_wpp_notmem_0061 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_022 x y A R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb084_alpha_dummy_022, fv_syn_cnnc] using (nb084_compact_fv_empty_0007 x y A R)

theorem nb084_wpp_notmem_0062 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_017 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb084_alpha_dummy_017, fv_syn_cnnc] using (nb084_compact_fv_empty_0008 A B R)

theorem nb084_wpp_notmem_0063 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_019 x y A R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb084_alpha_dummy_019, fv_syn_cnnc] using (nb084_compact_fv_empty_0009 x y A R)

theorem nb084_wpp_notmem_0064 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_018 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb084_alpha_dummy_018, fv_syn_cnnc] using (nb084_compact_fv_empty_0010 A B R)

theorem nb084_wpp_notmem_0065 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_020 x y A R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb084_alpha_dummy_020, fv_syn_cnnc] using (nb084_compact_fv_empty_0011 x y A R)

theorem nb084_wpp_notmem_0066 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_010 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb084_alpha_dummy_010, fv_syn_cnnc] using (nb084_compact_fv_empty_0012 A B R)

theorem nb084_wpp_notmem_0067 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_012 x y A R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb084_alpha_dummy_012, fv_syn_cnnc] using (nb084_compact_fv_empty_0013 x y A R)

theorem nb084_wpp_notmem_0068 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_009 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb084_alpha_dummy_009, fv_syn_cnnc] using (nb084_compact_fv_empty_0014 A B R)

theorem nb084_wpp_notmem_0069 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_011 x y A R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb084_alpha_dummy_011, fv_syn_cnnc] using (nb084_compact_fv_empty_0015 x y A R)

theorem nb084_wpp_notmem_0070 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_015 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb084_alpha_dummy_015, fv_syn_cnnc] using (nb084_compact_fv_empty_0016 A B R)

theorem nb084_wpp_notmem_0071 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_016 x y A R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb084_alpha_dummy_016, fv_syn_cnnc] using (nb084_compact_fv_empty_0017 x y A R)

theorem nb084_wpp_notmem_0072 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_013 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb084_alpha_dummy_013, fv_syn_cnnc] using (nb084_compact_fv_empty_0018 A B R)

theorem nb084_wpp_notmem_0073 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_014 x y A R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb084_alpha_dummy_014, fv_syn_cnnc] using (nb084_compact_fv_empty_0019 x y A R)

theorem nb084_wpp_notmem_0074 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_004 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb084_alpha_dummy_004, fv_syn_cnnc] using (nb084_compact_fv_empty_0020 A B R)

theorem nb084_wpp_notmem_0075 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_006 x y A R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb084_alpha_dummy_006, fv_syn_cnnc] using (nb084_compact_fv_empty_0021 x y A R)

theorem nb084_wpp_notmem_0076 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_003 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb084_alpha_dummy_003, fv_syn_cnnc] using (nb084_compact_fv_empty_0022 A B R)

theorem nb084_wpp_notmem_0077 (x : Var) (y : Var) (A : Class) (R : Class) : (nb084_alpha_dummy_005 x y A R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb084_alpha_dummy_005, fv_syn_cnnc] using (nb084_compact_fv_empty_0023 x y A R)

theorem nb084_wpp_notmem_0078 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_002 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb084_alpha_dummy_002, fv_syn_cnnc] using (nb084_compact_fv_empty_0024 A B R)

theorem nb084_wpp_notmem_0079 (y : Var) : y ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb084_compact_fv_empty_0025 y)

theorem nb084_wpp_notmem_0080 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_001 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb084_alpha_dummy_001, fv_syn_cnnc] using (nb084_compact_fv_empty_0026 A B R)

theorem nb084_wpp_notmem_0081 (x : Var) : x ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb084_compact_fv_empty_0027 x)

theorem nb084_wpp_notmem_0082 (A : Class) (B : Class) (R : Class) : (nb084_alpha_dummy_000 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb084_alpha_dummy_000, fv_syn_cnnc] using (nb084_compact_fv_empty_0028 A B R)

theorem nb084_wpp_notmem_0083 (d : Var) : d ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb084_compact_fv_empty_0029 d)

theorem nb084_compact_envfresh_0007 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (d : Var) : TEnvFresh [((nb084_alpha_dummy_021 A B R), (nb084_alpha_dummy_022 x y A R)), ((nb084_alpha_dummy_017 A B R), (nb084_alpha_dummy_019 x y A R)), ((nb084_alpha_dummy_018 A B R), (nb084_alpha_dummy_020 x y A R)), ((nb084_alpha_dummy_010 A B R), (nb084_alpha_dummy_012 x y A R)), ((nb084_alpha_dummy_009 A B R), (nb084_alpha_dummy_011 x y A R)), ((nb084_alpha_dummy_015 A B R), (nb084_alpha_dummy_016 x y A R)), ((nb084_alpha_dummy_013 A B R), (nb084_alpha_dummy_014 x y A R)), ((nb084_alpha_dummy_004 A B R), (nb084_alpha_dummy_006 x y A R)), ((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)), ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x), ((nb084_alpha_dummy_000 A B R), d)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb084_alpha_dummy_021 A B R) (nb084_alpha_dummy_022 x y A R) (nb084_wpp_notmem_0060 A B R) (nb084_wpp_notmem_0061 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_017 A B R) (nb084_alpha_dummy_019 x y A R) (nb084_wpp_notmem_0062 A B R) (nb084_wpp_notmem_0063 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_018 A B R) (nb084_alpha_dummy_020 x y A R) (nb084_wpp_notmem_0064 A B R) (nb084_wpp_notmem_0065 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_010 A B R) (nb084_alpha_dummy_012 x y A R) (nb084_wpp_notmem_0066 A B R) (nb084_wpp_notmem_0067 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_009 A B R) (nb084_alpha_dummy_011 x y A R) (nb084_wpp_notmem_0068 A B R) (nb084_wpp_notmem_0069 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_015 A B R) (nb084_alpha_dummy_016 x y A R) (nb084_wpp_notmem_0070 A B R) (nb084_wpp_notmem_0071 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_013 A B R) (nb084_alpha_dummy_014 x y A R) (nb084_wpp_notmem_0072 A B R) (nb084_wpp_notmem_0073 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_004 A B R) (nb084_alpha_dummy_006 x y A R) (nb084_wpp_notmem_0074 A B R) (nb084_wpp_notmem_0075 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_003 A B R) (nb084_alpha_dummy_005 x y A R) (nb084_wpp_notmem_0076 A B R) (nb084_wpp_notmem_0077 x y A R) (TEnvFresh.consFresh (nb084_alpha_dummy_002 A B R) y (nb084_wpp_notmem_0078 A B R) (nb084_wpp_notmem_0079 y) (TEnvFresh.consFresh (nb084_alpha_dummy_001 A B R) x (nb084_wpp_notmem_0080 A B R) (nb084_wpp_notmem_0081 x) (TEnvFresh.consFresh (nb084_alpha_dummy_000 A B R) d (nb084_wpp_notmem_0082 A B R) (nb084_wpp_notmem_0083 d) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))

noncomputable def nb084_wpp_refl_0002 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (d : Var) : TReflOn [((nb084_alpha_dummy_021 A B R), (nb084_alpha_dummy_022 x y A R)), ((nb084_alpha_dummy_017 A B R), (nb084_alpha_dummy_019 x y A R)), ((nb084_alpha_dummy_018 A B R), (nb084_alpha_dummy_020 x y A R)), ((nb084_alpha_dummy_010 A B R), (nb084_alpha_dummy_012 x y A R)), ((nb084_alpha_dummy_009 A B R), (nb084_alpha_dummy_011 x y A R)), ((nb084_alpha_dummy_015 A B R), (nb084_alpha_dummy_016 x y A R)), ((nb084_alpha_dummy_013 A B R), (nb084_alpha_dummy_014 x y A R)), ((nb084_alpha_dummy_004 A B R), (nb084_alpha_dummy_006 x y A R)), ((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)), ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x), ((nb084_alpha_dummy_000 A B R), d)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb084_compact_envfresh_0007 x y A B R d)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
