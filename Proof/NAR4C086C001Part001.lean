import NominalAlphaCompactEnvFreshSupport002
import NominalAlphaTransport
import WPPCompactSourceSyntax
import WPPCompactSyntaxFVExplicit
import CoreFVSimp
import CompactSyntaxFVDisable
import ReplaySupport.Basic
import AlphaFocusedSupport
import FocusedFVPaths

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

noncomputable def nb086_alpha_dummy_000 (A : Class) (B : Class) (C : Class) (R : Class) : Var := (freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0)

noncomputable def nb086_alpha_dummy_001 (A : Class) (B : Class) (C : Class) (R : Class) : Var := (freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1)

noncomputable def nb086_alpha_dummy_002 (A : Class) (B : Class) (C : Class) (R : Class) : Var := (freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb086_alpha_dummy_001 A B C R))).fv) 0)

noncomputable def nb086_alpha_dummy_003 (x : Var) (A : Class) (B : Class) (R : Class) : Var := (freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv x)).fv) 0)

theorem nb086_fresh_000 (A : Class) (B : Class) (C : Class) (R : Class) : (nb086_alpha_dummy_002 A B C R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb086_alpha_dummy_001 A B C R))).fv) := by
  simpa only [nb086_alpha_dummy_002] using freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb086_alpha_dummy_001 A B C R))).fv) 0

theorem nb086_fresh_001 (x : Var) (A : Class) (B : Class) (R : Class) : (nb086_alpha_dummy_003 x A B R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb086_alpha_dummy_003] using freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv x)).fv) 0

theorem nb086_fresh_002 (A : Class) (B : Class) (C : Class) (R : Class) : (nb086_alpha_dummy_000 A B C R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) := by
  simpa only [nb086_alpha_dummy_000] using freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0

theorem nb086_fresh_003 (A : Class) (B : Class) (C : Class) (R : Class) : (nb086_alpha_dummy_001 A B C R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) := by
  simpa only [nb086_alpha_dummy_001] using freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1

theorem nb086_distinct_004 (A : Class) (B : Class) (C : Class) (R : Class) : (nb086_alpha_dummy_000 A B C R) ≠ (nb086_alpha_dummy_001 A B C R) := by
  simpa only [nb086_alpha_dummy_000, nb086_alpha_dummy_001] using
    (freshVar_injective ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) (i := 0) (j := 1) (by decide))

theorem nb086_support_mem_0000 (A : Class) (B : Class) (C : Class) (R : Class) : (nb086_alpha_dummy_001 A B C R) ∈ ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb086_alpha_dummy_001 A B C R))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb086_support_mem_0001 (x : Var) (A : Class) (B : Class) (R : Class) : x ∈ ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv x)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb086_focused_notmem_0000 (A : Class) (B : Class) (C : Class) (R : Class) : (nb086_alpha_dummy_001 A B C R) ∉ C.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun u hu => Finset.mem_union_right _ (hu))

theorem nb086_focused_notmem_0001 (A : Class) (B : Class) (C : Class) (R : Class) : (nb086_alpha_dummy_000 A B C R) ∉ C.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_right _ (hu))

theorem nb086_compact_envfresh_0000 (x : Var) (A : Class) (B : Class) (C : Class) (R : Class) (q : Var) (dv_C_q : q ∉ C.fv) (dv_C_x : x ∉ C.fv) : TEnvFresh [((nb086_alpha_dummy_001 A B C R), x), ((nb086_alpha_dummy_000 A B C R), q)] C.fv := by
  exact (TEnvFresh.consFresh (nb086_alpha_dummy_001 A B C R) x (nb086_focused_notmem_0000 A B C R) dv_C_x (TEnvFresh.consFresh (nb086_alpha_dummy_000 A B C R) q (nb086_focused_notmem_0001 A B C R) dv_C_q (TEnvFresh.nil C.fv)))

noncomputable def nb086_focused_refl_0000 (x : Var) (A : Class) (B : Class) (C : Class) (R : Class) (q : Var) (dv_C_q : q ∉ C.fv) (dv_C_x : x ∉ C.fv) : TReflOn [((nb086_alpha_dummy_001 A B C R), x), ((nb086_alpha_dummy_000 A B C R), q)] C.fv :=
  TEnvFresh.reflOn (nb086_compact_envfresh_0000 x A B C R q dv_C_q dv_C_x)

theorem nb086_focused_notmem_0002 (A : Class) (B : Class) (C : Class) (R : Class) : (nb086_alpha_dummy_002 A B C R) ∉ A.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb086_alpha_dummy_001 A B C R))).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb086_focused_notmem_0003 (A : Class) (B : Class) (C : Class) (R : Class) : (nb086_alpha_dummy_002 A B C R) ∉ B.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb086_alpha_dummy_001 A B C R))).fv) 0 ∉ B.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb086_focused_notmem_0004 (A : Class) (B : Class) (C : Class) (R : Class) : (nb086_alpha_dummy_002 A B C R) ∉ R.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb086_alpha_dummy_001 A B C R))).fv) 0 ∉ R.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb086_wpp_notmem_0000 (A : Class) (B : Class) (C : Class) (R : Class) : (nb086_alpha_dummy_002 A B C R) ∉ ((syn_cfdif R A B)).fv := by
  simpa only [nb086_alpha_dummy_002, fv_syn_cfdif, Finset.mem_union, not_or] using (And.intro (And.intro (nb086_focused_notmem_0002 A B C R) (nb086_focused_notmem_0003 A B C R)) (nb086_focused_notmem_0004 A B C R))

theorem nb086_focused_notmem_0005 (x : Var) (A : Class) (B : Class) (R : Class) : (nb086_alpha_dummy_003 x A B R) ∉ A.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv x)).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb086_focused_notmem_0006 (x : Var) (A : Class) (B : Class) (R : Class) : (nb086_alpha_dummy_003 x A B R) ∉ B.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv x)).fv) 0 ∉ B.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb086_focused_notmem_0007 (x : Var) (A : Class) (B : Class) (R : Class) : (nb086_alpha_dummy_003 x A B R) ∉ R.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv x)).fv) 0 ∉ R.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb086_wpp_notmem_0001 (x : Var) (A : Class) (B : Class) (R : Class) : (nb086_alpha_dummy_003 x A B R) ∉ ((syn_cfdif R A B)).fv := by
  simpa only [nb086_alpha_dummy_003, fv_syn_cfdif, Finset.mem_union, not_or] using (And.intro (And.intro (nb086_focused_notmem_0005 x A B R) (nb086_focused_notmem_0006 x A B R)) (nb086_focused_notmem_0007 x A B R))

theorem nb086_focused_notmem_0008 (A : Class) (B : Class) (C : Class) (R : Class) : (nb086_alpha_dummy_001 A B C R) ∉ A.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb086_focused_notmem_0009 (A : Class) (B : Class) (C : Class) (R : Class) : (nb086_alpha_dummy_001 A B C R) ∉ B.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1 ∉ B.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb086_focused_notmem_0010 (A : Class) (B : Class) (C : Class) (R : Class) : (nb086_alpha_dummy_001 A B C R) ∉ R.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1 ∉ R.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb086_wpp_notmem_0002 (A : Class) (B : Class) (C : Class) (R : Class) : (nb086_alpha_dummy_001 A B C R) ∉ ((syn_cfdif R A B)).fv := by
  simpa only [nb086_alpha_dummy_001, fv_syn_cfdif, Finset.mem_union, not_or] using (And.intro (And.intro (nb086_focused_notmem_0008 A B C R) (nb086_focused_notmem_0009 A B C R)) (nb086_focused_notmem_0010 A B C R))

theorem nb086_wpp_notmem_0003 (x : Var) (A : Class) (B : Class) (R : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_R_x : x ∉ R.fv) : x ∉ ((syn_cfdif R A B)).fv := by
  simpa only [fv_syn_cfdif, Finset.mem_union, not_or] using (And.intro (And.intro dv_A_x dv_B_x) dv_R_x)

theorem nb086_focused_notmem_0011 (A : Class) (B : Class) (C : Class) (R : Class) : (nb086_alpha_dummy_000 A B C R) ∉ A.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb086_focused_notmem_0012 (A : Class) (B : Class) (C : Class) (R : Class) : (nb086_alpha_dummy_000 A B C R) ∉ B.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ B.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb086_focused_notmem_0013 (A : Class) (B : Class) (C : Class) (R : Class) : (nb086_alpha_dummy_000 A B C R) ∉ R.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ R.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb086_wpp_notmem_0004 (A : Class) (B : Class) (C : Class) (R : Class) : (nb086_alpha_dummy_000 A B C R) ∉ ((syn_cfdif R A B)).fv := by
  simpa only [nb086_alpha_dummy_000, fv_syn_cfdif, Finset.mem_union, not_or] using (And.intro (And.intro (nb086_focused_notmem_0011 A B C R) (nb086_focused_notmem_0012 A B C R)) (nb086_focused_notmem_0013 A B C R))

theorem nb086_wpp_notmem_0005 (A : Class) (B : Class) (R : Class) (q : Var) (dv_A_q : q ∉ A.fv) (dv_B_q : q ∉ B.fv) (dv_R_q : q ∉ R.fv) : q ∉ ((syn_cfdif R A B)).fv := by
  simpa only [fv_syn_cfdif, Finset.mem_union, not_or] using (And.intro (And.intro dv_A_q dv_B_q) dv_R_q)

theorem nb086_compact_envfresh_0001 (x : Var) (A : Class) (B : Class) (C : Class) (R : Class) (q : Var) (dv_A_q : q ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_B_q : q ∉ B.fv) (dv_B_x : x ∉ B.fv) (dv_R_q : q ∉ R.fv) (dv_R_x : x ∉ R.fv) : TEnvFresh [((nb086_alpha_dummy_002 A B C R), (nb086_alpha_dummy_003 x A B R)), ((nb086_alpha_dummy_001 A B C R), x), ((nb086_alpha_dummy_000 A B C R), q)] ((syn_cfdif R A B)).fv := by
  exact (TEnvFresh.consFresh (nb086_alpha_dummy_002 A B C R) (nb086_alpha_dummy_003 x A B R) (nb086_wpp_notmem_0000 A B C R) (nb086_wpp_notmem_0001 x A B R) (TEnvFresh.consFresh (nb086_alpha_dummy_001 A B C R) x (nb086_wpp_notmem_0002 A B C R) (nb086_wpp_notmem_0003 x A B R dv_A_x dv_B_x dv_R_x) (TEnvFresh.consFresh (nb086_alpha_dummy_000 A B C R) q (nb086_wpp_notmem_0004 A B C R) (nb086_wpp_notmem_0005 A B R q dv_A_q dv_B_q dv_R_q) (TEnvFresh.nil ((syn_cfdif R A B)).fv))))

noncomputable def nb086_wpp_refl_0000 (x : Var) (A : Class) (B : Class) (C : Class) (R : Class) (q : Var) (dv_A_q : q ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_B_q : q ∉ B.fv) (dv_B_x : x ∉ B.fv) (dv_R_q : q ∉ R.fv) (dv_R_x : x ∉ R.fv) : TReflOn [((nb086_alpha_dummy_002 A B C R), (nb086_alpha_dummy_003 x A B R)), ((nb086_alpha_dummy_001 A B C R), x), ((nb086_alpha_dummy_000 A B C R), q)] ((syn_cfdif R A B)).fv :=
  TEnvFresh.reflOn (nb086_compact_envfresh_0001 x A B C R q dv_A_q dv_A_x dv_B_q dv_B_x dv_R_q dv_R_x)

noncomputable def nominal_df_fdcode
    (x : Var) (A : Class) (B : Class) (C : Class) (R : Class) (q : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_q : q ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_B_q : q ∉ B.fv) (dv_B_x : x ∉ B.fv) (dv_C_R : Disjoint C.fv R.fv) (dv_C_q : q ∉ C.fv) (dv_C_x : x ∉ C.fv) (dv_R_q : q ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_q_x : q ≠ x) :
    Nominal.NPrf (.classEq (syn_cfdcode R A B C) (.cab q (syn_wrex x C (.classEq (.cv q) (syn_cfdrow R A B (.cv x)))))) := by
  exact Nominal.alphaClassEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb086_alpha_dummy_001 A B C R), x), ((nb086_alpha_dummy_000 A B C R), q)] C (nb086_focused_refl_0000 x A B C R q dv_C_q dv_C_x))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) (by decide)) dv_q_x (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb086_alpha_dummy_002 A B C R), (nb086_alpha_dummy_003 x A B R)), ((nb086_alpha_dummy_001 A B C R), x), ((nb086_alpha_dummy_000 A B C R), q)] (syn_cfdif R A B) (nb086_wpp_refl_0000 x A B C R q dv_A_q dv_A_x dv_B_q dv_B_x dv_R_q dv_R_x))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb086_support_mem_0000 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb086_support_mem_0001 x A B R) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.cv (TAlphaVar.here _ _ _)))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
