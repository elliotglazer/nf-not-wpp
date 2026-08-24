import NominalWPPReplayChunk007

set_option maxRecDepth 20000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

noncomputable def g_unineq
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (syn_wb (syn_wa (.classEq (syn_cun A C) (syn_cun B C)) (.classEq (syn_cin A C) (syn_cin B C))) (.classEq A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_eleq2 (syn_cin A C) (syn_cin B C) (.cv x)
  have p0001 :=
    @g_elin (.cv x) A C
  have p0002 :=
    @g_elin (.cv x) B C
  have p0003 :=
    @g_n_3bitr3g (.classEq (syn_cin A C) (syn_cin B C)) (.classMem (.cv x) (syn_cin A C)) (.classMem (.cv x) (syn_cin B C)) (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) C)) (syn_wa (.classMem (.cv x) B) (.classMem (.cv x) C)) p0000 p0001 p0002
  have p0004 :=
    @g_iba (.classMem (.cv x) C) (.classMem (.cv x) A)
  have p0005 :=
    @g_iba (.classMem (.cv x) C) (.classMem (.cv x) B)
  have p0006 :=
    @g_bibi12d (.classMem (.cv x) C) (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) C)) (.classMem (.cv x) B) (syn_wa (.classMem (.cv x) B) (.classMem (.cv x) C)) p0004 p0005
  have p0007 :=
    @g_syl5ibr (.classEq (syn_cin A C) (syn_cin B C)) (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C) (syn_wb (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) C)) (syn_wa (.classMem (.cv x) B) (.classMem (.cv x) C))) p0003 p0006
  have p0008 :=
    @g_adantld (.classMem (.cv x) C) (.classEq (syn_cin A C) (syn_cin B C)) (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classEq (syn_cun A C) (syn_cun B C)) p0007
  have p0009 :=
    @g_uncom A C
  have p0010 :=
    @g_uncom B C
  have p0011 :=
    @g_eqeq12i (syn_cun A C) (syn_cun C A) (syn_cun B C) (syn_cun C B) p0009 p0010
  have p0012 :=
    @g_eleq2 (syn_cun C A) (syn_cun C B) (.cv x)
  have p0013 :=
    @g_sylbi (.classEq (syn_cun A C) (syn_cun B C)) (.classEq (syn_cun C A) (syn_cun C B)) (syn_wb (.classMem (.cv x) (syn_cun C A)) (.classMem (.cv x) (syn_cun C B))) p0011 p0012
  have p0014 :=
    @g_elun (.cv x) C A
  have p0015 :=
    @g_elun (.cv x) C B
  have p0016 :=
    @g_n_3bitr3g (.classEq (syn_cun A C) (syn_cun B C)) (.classMem (.cv x) (syn_cun C A)) (.classMem (.cv x) (syn_cun C B)) (syn_wo (.classMem (.cv x) C) (.classMem (.cv x) A)) (syn_wo (.classMem (.cv x) C) (.classMem (.cv x) B)) p0013 p0014 p0015
  have p0017 :=
    @g_biorf (.classMem (.cv x) C) (.classMem (.cv x) A)
  have p0018 :=
    @g_biorf (.classMem (.cv x) C) (.classMem (.cv x) B)
  have p0019 :=
    @g_bibi12d (.neg (.classMem (.cv x) C)) (.classMem (.cv x) A) (syn_wo (.classMem (.cv x) C) (.classMem (.cv x) A)) (.classMem (.cv x) B) (syn_wo (.classMem (.cv x) C) (.classMem (.cv x) B)) p0017 p0018
  have p0020 :=
    @g_syl5ibr (.classEq (syn_cun A C) (syn_cun B C)) (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)) (.neg (.classMem (.cv x) C)) (syn_wb (syn_wo (.classMem (.cv x) C) (.classMem (.cv x) A)) (syn_wo (.classMem (.cv x) C) (.classMem (.cv x) B))) p0016 p0019
  have p0021 :=
    @g_adantrd (.neg (.classMem (.cv x) C)) (.classEq (syn_cun A C) (syn_cun B C)) (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classEq (syn_cin A C) (syn_cin B C)) p0020
  have p0022 :=
    @g_pm2_61i (.classMem (.cv x) C) (.imp (syn_wa (.classEq (syn_cun A C) (syn_cun B C)) (.classEq (syn_cin A C) (syn_cin B C))) (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B))) p0008 p0021
  have p0023 :=
    @g_eqrdv (syn_wa (.classEq (syn_cun A C) (syn_cun B C)) (.classEq (syn_cin A C) (syn_cin B C))) x A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0022
  have p0024 :=
    @g_uneq1 A B C
  have p0025 :=
    @g_ineq1 A B C
  have p0026 :=
    @g_jca (.classEq A B) (.classEq (syn_cun A C) (syn_cun B C)) (.classEq (syn_cin A C) (syn_cin B C)) p0024 p0025
  have p0027 :=
    @g_impbii (syn_wa (.classEq (syn_cun A C) (syn_cun B C)) (.classEq (syn_cin A C) (syn_cin B C))) (.classEq A B) p0023 p0026
  exact p0027

noncomputable def g_difundir
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (syn_cdif (syn_cun A B) C) (syn_cun (syn_cdif A C) (syn_cdif B C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_indir A B (syn_cdif (syn_cvv) C)
  have p0001 :=
    @g_invdif (syn_cun A B) C
  have p0002 :=
    @g_invdif A C
  have p0003 :=
    @g_invdif B C
  have p0004 :=
    @g_uneq12i (syn_cin A (syn_cdif (syn_cvv) C)) (syn_cdif A C) (syn_cin B (syn_cdif (syn_cvv) C)) (syn_cdif B C) p0002 p0003
  have p0005 :=
    @g_n_3eqtr3i (syn_cin (syn_cun A B) (syn_cdif (syn_cvv) C)) (syn_cun (syn_cin A (syn_cdif (syn_cvv) C)) (syn_cin B (syn_cdif (syn_cvv) C))) (syn_cdif (syn_cun A B) C) (syn_cun (syn_cdif A C) (syn_cdif B C)) p0000 p0001 p0004
  exact p0005

noncomputable def g_unab
    (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.classEq (syn_cun (.cab x ph) (.cab x ps)) (.cab x (syn_wo ph ps))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({x} : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_ps : y ∉ ps.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have p0000 :=
    @g_sbor ph ps x y
  have p0001 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClabGoal, syn_wb, syn_wsb, syn_wa, syn_wex, Wff.biimp, Wff.ex, Wff.conj, Wff.neg, sbDefiniens] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural y x (syn_wo ph ps)))
  have p0002 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClabGoal, syn_wb, syn_wsb, syn_wa, syn_wex, Wff.biimp, Wff.ex, Wff.conj, Wff.neg, sbDefiniens] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural y x ph))
  have p0003 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClabGoal, syn_wb, syn_wsb, syn_wa, syn_wex, Wff.biimp, Wff.ex, Wff.conj, Wff.neg, sbDefiniens] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural y x ps))
  have p0004 :=
    @g_orbi12i (.classMem (.cv y) (.cab x ph)) (syn_wsb y x ph) (.classMem (.cv y) (.cab x ps)) (syn_wsb y x ps) p0002 p0003
  have p0005 :=
    @g_n_3bitr4ri (syn_wsb y x (syn_wo ph ps)) (syn_wo (syn_wsb y x ph) (syn_wsb y x ps)) (.classMem (.cv y) (.cab x (syn_wo ph ps))) (syn_wo (.classMem (.cv y) (.cab x ph)) (.classMem (.cv y) (.cab x ps))) p0000 p0001 p0004
  have p0006 :=
    @g_uneqri y (.cab x ph) (.cab x ps) (.cab x (syn_wo ph ps)) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0005
  exact p0006

noncomputable def g_inab
    (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.classEq (syn_cin (.cab x ph) (.cab x ps)) (.cab x (syn_wa ph ps))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({x} : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_ps : y ∉ ps.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have p0000 :=
    @g_sban ph ps x y
  have p0001 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClabGoal, syn_wb, syn_wsb, syn_wa, syn_wex, Wff.biimp, Wff.ex, Wff.conj, Wff.neg, sbDefiniens] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural y x (syn_wa ph ps)))
  have p0002 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClabGoal, syn_wb, syn_wsb, syn_wa, syn_wex, Wff.biimp, Wff.ex, Wff.conj, Wff.neg, sbDefiniens] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural y x ph))
  have p0003 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClabGoal, syn_wb, syn_wsb, syn_wa, syn_wex, Wff.biimp, Wff.ex, Wff.conj, Wff.neg, sbDefiniens] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural y x ps))
  have p0004 :=
    @g_anbi12i (.classMem (.cv y) (.cab x ph)) (syn_wsb y x ph) (.classMem (.cv y) (.cab x ps)) (syn_wsb y x ps) p0002 p0003
  have p0005 :=
    @g_n_3bitr4ri (syn_wsb y x (syn_wa ph ps)) (syn_wa (syn_wsb y x ph) (syn_wsb y x ps)) (.classMem (.cv y) (.cab x (syn_wa ph ps))) (syn_wa (.classMem (.cv y) (.cab x ph)) (.classMem (.cv y) (.cab x ps))) p0000 p0001 p0004
  have p0006 :=
    @g_ineqri y (.cab x ph) (.cab x ps) (.cab x (syn_wa ph ps)) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0005
  exact p0006

noncomputable def g_difab
    (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.classEq (syn_cdif (.cab x ph) (.cab x ps)) (.cab x (syn_wa ph (.neg ps)))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({x} : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_ps : y ∉ ps.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have p0000 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClabGoal, syn_wb, syn_wsb, syn_wa, syn_wex, Wff.biimp, Wff.ex, Wff.conj, Wff.neg, sbDefiniens] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural y x (syn_wa ph (.neg ps))))
  have p0001 :=
    @g_sban ph (.neg ps) x y
  have p0002 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClabGoal, syn_wb, syn_wsb, syn_wa, syn_wex, Wff.biimp, Wff.ex, Wff.conj, Wff.neg, sbDefiniens] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural y x ph))
  have p0003 :=
    @g_bicomi (.classMem (.cv y) (.cab x ph)) (syn_wsb y x ph) p0002
  have p0004 :=
    @g_sbn ps x y
  have p0005 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClabGoal, syn_wb, syn_wsb, syn_wa, syn_wex, Wff.biimp, Wff.ex, Wff.conj, Wff.neg, sbDefiniens] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural y x ps))
  have p0006 :=
    @g_xchbinxr (syn_wsb y x (.neg ps)) (syn_wsb y x ps) (.classMem (.cv y) (.cab x ps)) p0004 p0005
  have p0007 :=
    @g_anbi12i (syn_wsb y x ph) (.classMem (.cv y) (.cab x ph)) (syn_wsb y x (.neg ps)) (.neg (.classMem (.cv y) (.cab x ps))) p0003 p0006
  have p0008 :=
    @g_n_3bitrri (.classMem (.cv y) (.cab x (syn_wa ph (.neg ps)))) (syn_wsb y x (syn_wa ph (.neg ps))) (syn_wa (syn_wsb y x ph) (syn_wsb y x (.neg ps))) (syn_wa (.classMem (.cv y) (.cab x ph)) (.neg (.classMem (.cv y) (.cab x ps)))) p0000 p0001 p0007
  have p0009 :=
    @g_difeqri y (.cab x ph) (.cab x ps) (.cab x (syn_wa ph (.neg ps))) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0008
  exact p0009

noncomputable def g_complab
    (ph : Wff) (x : Var) :
    Nominal.NPrf (.classEq (syn_ccompl (.cab x ph)) (.cab x (.neg ph))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have p0000 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClabGoal, syn_wb, syn_wsb, syn_wa, syn_wex, Wff.biimp, Wff.ex, Wff.conj, Wff.neg, sbDefiniens] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural y x ph))
  have p0001 :=
    @g_notbii (.classMem (.cv y) (.cab x ph)) (syn_wsb y x ph) p0000
  have p0002 :=
    @g_sbn ph x y
  have p0003 :=
    @g_bitr4i (.neg (.classMem (.cv y) (.cab x ph))) (.neg (syn_wsb y x ph)) (syn_wsb y x (.neg ph)) p0001 p0002
  have p0004 :=
    @g_vex y
  have p0005 :=
    @g_elcompl (.cv y) (.cab x ph) p0004
  have p0006 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClabGoal, syn_wb, syn_wsb, syn_wa, syn_wex, Wff.biimp, Wff.ex, Wff.conj, Wff.neg, sbDefiniens] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural y x (.neg ph)))
  have p0007 :=
    @g_n_3bitr4i (.neg (.classMem (.cv y) (.cab x ph))) (syn_wsb y x (.neg ph)) (.classMem (.cv y) (syn_ccompl (.cab x ph))) (.classMem (.cv y) (.cab x (.neg ph))) p0003 p0005 p0006
  have p0008 :=
    @g_eqriv y (syn_ccompl (.cab x ph)) (.cab x (.neg ph)) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CoreFVSimp.fv_class_cab, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0007
  exact p0008

noncomputable def g_notab
    (ph : Wff) (x : Var) :
    Nominal.NPrf (.classEq (.cab x (.neg ph)) (syn_cdif (syn_cvv) (.cab x ph))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var)
  have p0000 :=
    (by simpa [syn_crab] using (Nominal.classEqRefl (syn_crab x (syn_cvv) (.neg ph))))
  have p0001 :=
    @g_rabab (.neg ph) x
  have p0002 :=
    @g_eqtr3i (syn_crab x (syn_cvv) (.neg ph)) (.cab x (syn_wa (.classMem (.cv x) (syn_cvv)) (.neg ph))) (.cab x (.neg ph)) p0000 p0001
  have p0003 :=
    @g_difab (.classMem (.cv x) (syn_cvv)) ph x
  have p0004 :=
    @g_abid2 x (syn_cvv) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0005 :=
    @g_difeq1i (.cab x (.classMem (.cv x) (syn_cvv))) (syn_cvv) (.cab x ph) p0004
  have p0006 :=
    @g_eqtr3i (syn_cdif (.cab x (.classMem (.cv x) (syn_cvv))) (.cab x ph)) (.cab x (syn_wa (.classMem (.cv x) (syn_cvv)) (.neg ph))) (syn_cdif (syn_cvv) (.cab x ph)) p0003 p0005
  have p0007 :=
    @g_eqtr3i (.cab x (syn_wa (.classMem (.cv x) (syn_cvv)) (.neg ph))) (.cab x (.neg ph)) (syn_cdif (syn_cvv) (.cab x ph)) p0002 p0006
  exact p0007

noncomputable def g_unrab
    (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf (.classEq (syn_cun (syn_crab x A ph) (syn_crab x A ps)) (syn_crab x A (syn_wo ph ps))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({x} : Finset Var) ∪ A.fv
  have p0000 :=
    (by simpa [syn_crab] using (Nominal.classEqRefl (syn_crab x A ph)))
  have p0001 :=
    (by simpa [syn_crab] using (Nominal.classEqRefl (syn_crab x A ps)))
  have p0002 :=
    @g_uneq12i (syn_crab x A ph) (.cab x (syn_wa (.classMem (.cv x) A) ph)) (syn_crab x A ps) (.cab x (syn_wa (.classMem (.cv x) A) ps)) p0000 p0001
  have p0003 :=
    (by simpa [syn_crab] using (Nominal.classEqRefl (syn_crab x A (syn_wo ph ps))))
  have p0004 :=
    @g_unab (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) A) ps) x
  have p0005 :=
    @g_andi (.classMem (.cv x) A) ph ps
  have p0006 :=
    @g_abbii (syn_wa (.classMem (.cv x) A) (syn_wo ph ps)) (syn_wo (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) A) ps)) x p0005
  have p0007 :=
    @g_eqtr4i (syn_cun (.cab x (syn_wa (.classMem (.cv x) A) ph)) (.cab x (syn_wa (.classMem (.cv x) A) ps))) (.cab x (syn_wo (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) A) ps))) (.cab x (syn_wa (.classMem (.cv x) A) (syn_wo ph ps))) p0004 p0006
  have p0008 :=
    @g_eqtr4i (syn_crab x A (syn_wo ph ps)) (.cab x (syn_wa (.classMem (.cv x) A) (syn_wo ph ps))) (syn_cun (.cab x (syn_wa (.classMem (.cv x) A) ph)) (.cab x (syn_wa (.classMem (.cv x) A) ps))) p0003 p0007
  have p0009 :=
    @g_eqtr4i (syn_cun (syn_crab x A ph) (syn_crab x A ps)) (syn_cun (.cab x (syn_wa (.classMem (.cv x) A) ph)) (.cab x (syn_wa (.classMem (.cv x) A) ps))) (syn_crab x A (syn_wo ph ps)) p0002 p0008
  exact p0009

noncomputable def g_dfrab2
    (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (syn_crab x A ph) (syn_cin (.cab x ph) A)) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ A.fv
  have p0000 :=
    (by simpa [syn_crab] using (Nominal.classEqRefl (syn_crab x A ph)))
  have p0001 :=
    @g_inab (.classMem (.cv x) A) ph x
  have p0002 :=
    @g_abid2 x A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_ineq1i (.cab x (.classMem (.cv x) A)) A (.cab x ph) p0002
  have p0004 :=
    @g_eqtr3i (syn_cin (.cab x (.classMem (.cv x) A)) (.cab x ph)) (.cab x (syn_wa (.classMem (.cv x) A) ph)) (syn_cin A (.cab x ph)) p0001 p0003
  have p0005 :=
    @g_incom A (.cab x ph)
  have p0006 :=
    @g_n_3eqtri (syn_crab x A ph) (.cab x (syn_wa (.classMem (.cv x) A) ph)) (syn_cin A (.cab x ph)) (syn_cin (.cab x ph) A) p0000 p0004 p0005
  exact p0006

noncomputable def g_dfrab3
    (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (syn_crab x A ph) (syn_cin A (.cab x ph))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ A.fv
  have p0000 :=
    (by simpa [syn_crab] using (Nominal.classEqRefl (syn_crab x A ph)))
  have p0001 :=
    @g_inab (.classMem (.cv x) A) ph x
  have p0002 :=
    @g_abid2 x A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_ineq1i (.cab x (.classMem (.cv x) A)) A (.cab x ph) p0002
  have p0004 :=
    @g_n_3eqtr2i (syn_crab x A ph) (.cab x (syn_wa (.classMem (.cv x) A) ph)) (syn_cin (.cab x (.classMem (.cv x) A)) (.cab x ph)) (syn_cin A (.cab x ph)) p0000 p0001 p0003
  exact p0004

noncomputable def g_notrab
    (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (syn_cdif A (syn_crab x A ph)) (syn_crab x A (.neg ph))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_difab (.classMem (.cv x) A) ph x
  have p0001 :=
    @g_difin A (.cab x ph)
  have p0002 :=
    @g_dfrab3 ph x A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_difeq2i (syn_crab x A ph) (syn_cin A (.cab x ph)) A p0002
  have p0004 :=
    @g_abid2 x A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0005 :=
    @g_difeq1i (.cab x (.classMem (.cv x) A)) A (.cab x ph) p0004
  have p0006 :=
    @g_n_3eqtr4i (syn_cdif A (syn_cin A (.cab x ph))) (syn_cdif A (.cab x ph)) (syn_cdif A (syn_crab x A ph)) (syn_cdif (.cab x (.classMem (.cv x) A)) (.cab x ph)) p0001 p0003 p0005
  have p0007 :=
    (by simpa [syn_crab] using (Nominal.classEqRefl (syn_crab x A (.neg ph))))
  have p0008 :=
    @g_n_3eqtr4i (syn_cdif (.cab x (.classMem (.cv x) A)) (.cab x ph)) (.cab x (syn_wa (.classMem (.cv x) A) (.neg ph))) (syn_cdif A (syn_crab x A ph)) (syn_crab x A (.neg ph)) p0000 p0006 p0007
  exact p0008

noncomputable def g_compleqb
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (.classEq A B) (.classEq (syn_ccompl A) (syn_ccompl B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_compleq A B
  have p0001 :=
    @g_compleq (syn_ccompl A) (syn_ccompl B)
  have p0002 :=
    @g_dblcompl A
  have p0003 :=
    @g_dblcompl B
  have p0004 :=
    @g_n_3eqtr3g (.classEq (syn_ccompl A) (syn_ccompl B)) (syn_ccompl (syn_ccompl A)) (syn_ccompl (syn_ccompl B)) A B p0001 p0002 p0003
  have p0005 :=
    @g_impbii (.classEq A B) (.classEq (syn_ccompl A) (syn_ccompl B)) p0000 p0004
  exact p0005

noncomputable def g_necompl
    (A : Class) :
    Nominal.NPrf (syn_wne (syn_ccompl A) A) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have p0000 :=
    @g_pm5_19 (.classMem (.cv x) A)
  have p0001 :=
    @g_vex x
  have p0002 :=
    @g_elcompl (.cv x) A p0001
  have p0003 :=
    @g_bibi2i (.classMem (.cv x) (syn_ccompl A)) (.neg (.classMem (.cv x) A)) (.classMem (.cv x) A) p0002
  have p0004 :=
    @g_mtbir (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_ccompl A))) (syn_wb (.classMem (.cv x) A) (.neg (.classMem (.cv x) A))) p0000 p0003
  have p0005 :=
    @g_n_19_8a (.neg (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_ccompl A)))) x
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_dfcleq x A (syn_ccompl A) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0008 :=
    @g_necon3abii (.all x (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_ccompl A)))) A (syn_ccompl A) p0007
  have p0009 :=
    @g_exnal (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_ccompl A))) x
  have p0010 :=
    @g_bitr4i (syn_wne A (syn_ccompl A)) (.neg (.all x (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_ccompl A))))) (syn_wex x (.neg (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_ccompl A))))) p0008 p0009
  have p0011 :=
    @g_mpbir (syn_wne A (syn_ccompl A)) (syn_wex x (.neg (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_ccompl A))))) p0006 p0010
  have p0012 :=
    @g_necomi A (syn_ccompl A) p0011
  exact p0012

noncomputable def g_dfin5
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cin A B) (syn_ccompl (syn_cun (syn_ccompl A) (syn_ccompl B)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_dblcompl A
  have p0001 :=
    @g_dblcompl B
  have p0002 :=
    @g_nineq12i (syn_ccompl (syn_ccompl A)) A (syn_ccompl (syn_ccompl B)) B p0000 p0001
  have p0003 :=
    @g_compleqi (syn_cnin (syn_ccompl (syn_ccompl A)) (syn_ccompl (syn_ccompl B))) (syn_cnin A B) p0002
  have p0004 :=
    (by simpa [syn_cun] using (Nominal.classEqRefl (syn_cun (syn_ccompl A) (syn_ccompl B))))
  have p0005 :=
    @g_compleqi (syn_cun (syn_ccompl A) (syn_ccompl B)) (syn_cnin (syn_ccompl (syn_ccompl A)) (syn_ccompl (syn_ccompl B))) p0004
  have p0006 :=
    (by simpa [syn_cin] using (Nominal.classEqRefl (syn_cin A B)))
  have p0007 :=
    @g_n_3eqtr4ri (syn_ccompl (syn_cnin (syn_ccompl (syn_ccompl A)) (syn_ccompl (syn_ccompl B)))) (syn_ccompl (syn_cnin A B)) (syn_ccompl (syn_cun (syn_ccompl A) (syn_ccompl B))) (syn_cin A B) p0003 p0005 p0006
  exact p0007

noncomputable def g_dfun4
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cun A B) (syn_ccompl (syn_cin (syn_ccompl A) (syn_ccompl B)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_dfin5 (syn_ccompl A) (syn_ccompl B)
  have p0001 :=
    @g_compleqi (syn_cin (syn_ccompl A) (syn_ccompl B)) (syn_ccompl (syn_cun (syn_ccompl (syn_ccompl A)) (syn_ccompl (syn_ccompl B)))) p0000
  have p0002 :=
    @g_dblcompl (syn_cun (syn_ccompl (syn_ccompl A)) (syn_ccompl (syn_ccompl B)))
  have p0003 :=
    @g_dblcompl A
  have p0004 :=
    @g_dblcompl B
  have p0005 :=
    @g_uneq12i (syn_ccompl (syn_ccompl A)) A (syn_ccompl (syn_ccompl B)) B p0003 p0004
  have p0006 :=
    @g_n_3eqtrri (syn_ccompl (syn_cin (syn_ccompl A) (syn_ccompl B))) (syn_ccompl (syn_ccompl (syn_cun (syn_ccompl (syn_ccompl A)) (syn_ccompl (syn_ccompl B))))) (syn_cun (syn_ccompl (syn_ccompl A)) (syn_ccompl (syn_ccompl B))) (syn_cun A B) p0001 p0002 p0005
  exact p0006

noncomputable def g_iunin
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_ccompl (syn_cun A B)) (syn_cin (syn_ccompl A) (syn_ccompl B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_dfin5 (syn_ccompl A) (syn_ccompl B)
  have p0001 :=
    @g_dblcompl A
  have p0002 :=
    @g_dblcompl B
  have p0003 :=
    @g_uneq12i (syn_ccompl (syn_ccompl A)) A (syn_ccompl (syn_ccompl B)) B p0001 p0002
  have p0004 :=
    @g_compleqi (syn_cun (syn_ccompl (syn_ccompl A)) (syn_ccompl (syn_ccompl B))) (syn_cun A B) p0003
  have p0005 :=
    @g_eqtr2i (syn_cin (syn_ccompl A) (syn_ccompl B)) (syn_ccompl (syn_cun (syn_ccompl (syn_ccompl A)) (syn_ccompl (syn_ccompl B)))) (syn_ccompl (syn_cun A B)) p0000 p0004
  exact p0005

noncomputable def g_iinun
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_ccompl (syn_cin A B)) (syn_cun (syn_ccompl A) (syn_ccompl B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_dfun4 (syn_ccompl A) (syn_ccompl B)
  have p0001 :=
    @g_dblcompl A
  have p0002 :=
    @g_dblcompl B
  have p0003 :=
    @g_ineq12i (syn_ccompl (syn_ccompl A)) A (syn_ccompl (syn_ccompl B)) B p0001 p0002
  have p0004 :=
    @g_compleqi (syn_cin (syn_ccompl (syn_ccompl A)) (syn_ccompl (syn_ccompl B))) (syn_cin A B) p0003
  have p0005 :=
    @g_eqtr2i (syn_cun (syn_ccompl A) (syn_ccompl B)) (syn_ccompl (syn_cin (syn_ccompl (syn_ccompl A)) (syn_ccompl (syn_ccompl B)))) (syn_ccompl (syn_cin A B)) p0000 p0004
  exact p0005

noncomputable def g_difsscompl
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wss (syn_cdif A B) (syn_ccompl B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    (by simpa [syn_cdif] using (Nominal.classEqRefl (syn_cdif A B)))
  have p0001 :=
    @g_inss2 A (syn_ccompl B)
  have p0002 :=
    @g_eqsstri (syn_cdif A B) (syn_cin A (syn_ccompl B)) (syn_ccompl B) p0000 p0001
  exact p0002

noncomputable def g_dfnul2
    (x : Var) :
    Nominal.NPrf (.classEq (syn_c0) (.cab x (.neg (.classEq (.cv x) (.cv x))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var)
  have p0000 :=
    (by simpa [syn_c0] using (Nominal.classEqRefl (syn_c0)))
  have p0001 :=
    @g_eleq2i (syn_c0) (syn_cdif (syn_cvv) (syn_cvv)) (.cv x) p0000
  have p0002 :=
    @g_eldif (.cv x) (syn_cvv) (syn_cvv)
  have p0003 :=
    @g_eqid (.cv x)
  have p0004 :=
    @g_pm3_24 (.classMem (.cv x) (syn_cvv))
  have p0005 :=
    @g_n_2th (.classEq (.cv x) (.cv x)) (.neg (syn_wa (.classMem (.cv x) (syn_cvv)) (.neg (.classMem (.cv x) (syn_cvv))))) p0003 p0004
  have p0006 :=
    @g_con2bii (.classEq (.cv x) (.cv x)) (syn_wa (.classMem (.cv x) (syn_cvv)) (.neg (.classMem (.cv x) (syn_cvv)))) p0005
  have p0007 :=
    @g_n_3bitri (.classMem (.cv x) (syn_c0)) (.classMem (.cv x) (syn_cdif (syn_cvv) (syn_cvv))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.neg (.classMem (.cv x) (syn_cvv)))) (.neg (.classEq (.cv x) (.cv x))) p0001 p0002 p0006
  have p0008 :=
    @g_eqabi (.neg (.classEq (.cv x) (.cv x))) x (syn_c0) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0007
  exact p0008

noncomputable def g_noel
    (A : Class) :
    Nominal.NPrf (.neg (.classMem A (syn_c0))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_eldifi A (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_eldifn A (syn_cvv) (syn_cvv)
  have p0002 :=
    @g_pm2_65i (.classMem A (syn_cdif (syn_cvv) (syn_cvv))) (.classMem A (syn_cvv)) p0000 p0001
  have p0003 :=
    (by simpa [syn_c0] using (Nominal.classEqRefl (syn_c0)))
  have p0004 :=
    @g_eleq2i (syn_c0) (syn_cdif (syn_cvv) (syn_cvv)) A p0003
  have p0005 :=
    @g_mtbir (.classMem A (syn_c0)) (.classMem A (syn_cdif (syn_cvv) (syn_cvv))) p0002 p0004
  exact p0005

noncomputable def g_n0i
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem B A) (.neg (.classEq A (syn_c0)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_noel B
  have p0001 :=
    @g_eleq2 A (syn_c0) B
  have p0002 :=
    @g_mtbiri (.classEq A (syn_c0)) (.classMem B A) (.classMem B (syn_c0)) p0000 p0001
  have p0003 :=
    @g_con2i (.classEq A (syn_c0)) (.classMem B A) p0002
  exact p0003

noncomputable def g_ne0i
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem B A) (syn_wne A (syn_c0))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_n0i A B
  have p0001 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne A (syn_c0))))
  have p0002 :=
    @g_sylibr (.classMem B A) (.neg (.classEq A (syn_c0))) (syn_wne A (syn_c0)) p0000 p0001
  exact p0002

noncomputable def g_vn0
     :
    Nominal.NPrf (syn_wne (syn_cvv) (syn_c0)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have p0000 :=
    @g_vex x
  have p0001 :=
    @g_ne0i (syn_cvv) (.cv x)
  have p0002 :=
    Nominal.mp p0000 p0001
  exact p0002

noncomputable def g_n0f
    (x : Var) (A : Class) (hyp_n0f_1 : Nominal.NPrf (syn_wnfc x A)) :
    Nominal.NPrf (syn_wb (syn_wne A (syn_c0)) (syn_wex x (.classMem (.cv x) A))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfcv x (syn_c0) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_cleqf x A (syn_c0) hyp_n0f_1 p0000
  have p0002 :=
    @g_noel (.cv x)
  have p0003 :=
    @g_nbn (.classMem (.cv x) (syn_c0)) (.classMem (.cv x) A) p0002
  have p0004 :=
    @g_albii (.neg (.classMem (.cv x) A)) (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_c0))) x p0003
  have p0005 :=
    @g_bitr4i (.classEq A (syn_c0)) (.all x (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_c0)))) (.all x (.neg (.classMem (.cv x) A))) p0001 p0004
  have p0006 :=
    @g_necon3abii (.all x (.neg (.classMem (.cv x) A))) A (syn_c0) p0005
  have p0007 :=
    (by simpa [syn_wb, syn_wex] using (Nominal.biimpRefl (syn_wex x (.classMem (.cv x) A))))
  have p0008 :=
    @g_bitr4i (syn_wne A (syn_c0)) (.neg (.all x (.neg (.classMem (.cv x) A)))) (syn_wex x (.classMem (.cv x) A)) p0006 p0007
  exact p0008

noncomputable def g_n0
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (syn_wne A (syn_c0)) (syn_wex x (.classMem (.cv x) A))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfcv x A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_n0f x A p0000
  exact p0001

noncomputable def g_neq0
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.neg (.classEq A (syn_c0))) (syn_wex x (.classMem (.cv x) A))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  have p0000 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne A (syn_c0))))
  have p0001 :=
    @g_n0 x A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0002 :=
    @g_bitr3i (.neg (.classEq A (syn_c0))) (syn_wne A (syn_c0)) (syn_wex x (.classMem (.cv x) A)) p0000 p0001
  exact p0002

noncomputable def g_rex0
    (ph : Wff) (x : Var) :
    Nominal.NPrf (.neg (syn_wrex x (syn_c0) ph)) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var)
  have p0000 :=
    @g_noel (.cv x)
  have p0001 :=
    @g_pm2_21i (.classMem (.cv x) (syn_c0)) (.neg ph) p0000
  have p0002 :=
    @g_nrex ph x (syn_c0) p0001
  exact p0002

noncomputable def g_eq0
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classEq A (syn_c0)) (.all x (.neg (.classMem (.cv x) A)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_neq0 x A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    (by simpa [syn_wb, syn_wex] using (Nominal.biimpRefl (syn_wex x (.classMem (.cv x) A))))
  have p0002 :=
    @g_bitri (.neg (.classEq A (syn_c0))) (syn_wex x (.classMem (.cv x) A)) (.neg (.all x (.neg (.classMem (.cv x) A)))) p0000 p0001
  have p0003 :=
    @g_con4bii (.classEq A (syn_c0)) (.all x (.neg (.classMem (.cv x) A))) p0002
  exact p0003

noncomputable def g_eqv
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classEq A (syn_cvv)) (.all x (.classMem (.cv x) A))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_dfcleq x A (syn_cvv) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_vex x
  have p0002 :=
    @g_tbt (.classMem (.cv x) (syn_cvv)) (.classMem (.cv x) A) p0001
  have p0003 :=
    @g_albii (.classMem (.cv x) A) (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_cvv))) x p0002
  have p0004 :=
    @g_bitr4i (.classEq A (syn_cvv)) (.all x (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_cvv)))) (.all x (.classMem (.cv x) A)) p0000 p0003
  exact p0004

noncomputable def g_abvor0
    (ph : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (syn_wo (.classEq (.cab x ph) (syn_cvv)) (.classEq (.cab x ph) (syn_c0))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var)
  have p0000 :=
    @g_id ph
  have p0001 :=
    @g_vex x
  have p0002 :=
    @g_a1i (.classMem (.cv x) (syn_cvv)) ph p0001
  have p0003 :=
    @g_n_2thd ph ph (.classMem (.cv x) (syn_cvv)) p0000 p0002
  have p0004 :=
    @g_eqabcdv ph ph x (syn_cvv) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0003
  have p0005 :=
    @g_con3i ph (.classEq (.cab x ph) (syn_cvv)) p0004
  have p0006 :=
    @g_id (.neg ph)
  have p0007 :=
    @g_noel (.cv x)
  have p0008 :=
    @g_a1i (.neg (.classMem (.cv x) (syn_c0))) (.neg ph) p0007
  have p0009 :=
    @g_n_2falsed (.neg ph) ph (.classMem (.cv x) (syn_c0)) p0006 p0008
  have p0010 :=
    @g_eqabcdv (.neg ph) ph x (syn_c0) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0009
  have p0011 :=
    @g_syl (.neg (.classEq (.cab x ph) (syn_cvv))) (.neg ph) (.classEq (.cab x ph) (syn_c0)) p0005 p0010
  have p0012 :=
    @g_orri (.classEq (.cab x ph) (syn_cvv)) (.classEq (.cab x ph) (syn_c0)) p0011
  exact p0012

noncomputable def g_abn0
    (ph : Wff) (x : Var) :
    Nominal.NPrf (syn_wb (syn_wne (.cab x ph) (syn_c0)) (syn_wex x ph)) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var)
  have p0000 :=
    @g_nfab1 ph x
  have p0001 :=
    @g_n0f x (.cab x ph) p0000
  have p0002 :=
    @g_abid ph x
  have p0003 :=
    @g_exbii (.classMem (.cv x) (.cab x ph)) ph x p0002
  have p0004 :=
    @g_bitri (syn_wne (.cab x ph) (syn_c0)) (syn_wex x (.classMem (.cv x) (.cab x ph))) (syn_wex x ph) p0001 p0003
  exact p0004

noncomputable def g_ab0
    (ph : Wff) (x : Var) :
    Nominal.NPrf (syn_wb (.classEq (.cab x ph) (syn_c0)) (.all x (.neg ph))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var)
  have p0000 :=
    @g_abn0 ph x
  have p0001 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (.cab x ph) (syn_c0))))
  have p0002 :=
    (by simpa [syn_wb, syn_wex] using (Nominal.biimpRefl (syn_wex x ph)))
  have p0003 :=
    @g_n_3bitr3i (syn_wne (.cab x ph) (syn_c0)) (syn_wex x ph) (.neg (.classEq (.cab x ph) (syn_c0))) (.neg (.all x (.neg ph))) p0000 p0001 p0002
  have p0004 :=
    @g_con4bii (.classEq (.cab x ph) (syn_c0)) (.all x (.neg ph)) p0003
  exact p0004

noncomputable def g_un0
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cun A (syn_c0)) A) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have p0000 :=
    @g_noel (.cv x)
  have p0001 :=
    @g_biorfi (.classMem (.cv x) (syn_c0)) (.classMem (.cv x) A) p0000
  have p0002 :=
    @g_bicomi (.classMem (.cv x) A) (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) (syn_c0))) p0001
  have p0003 :=
    @g_uneqri x A (syn_c0) A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0002
  exact p0003

noncomputable def g_in0
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cin A (syn_c0)) (syn_c0)) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have p0000 :=
    @g_noel (.cv x)
  have p0001 :=
    @g_bianfi (.classMem (.cv x) (syn_c0)) (.classMem (.cv x) A) p0000
  have p0002 :=
    @g_bicomi (.classMem (.cv x) (syn_c0)) (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) (syn_c0))) p0001
  have p0003 :=
    @g_ineqri x A (syn_c0) (syn_c0) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0002
  exact p0003

noncomputable def g_inv1
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cin A (syn_cvv)) A) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_inss1 A (syn_cvv)
  have p0001 :=
    @g_ssid A
  have p0002 :=
    @g_ssv A
  have p0003 :=
    @g_ssini A A (syn_cvv) p0001 p0002
  have p0004 :=
    @g_eqssi (syn_cin A (syn_cvv)) A p0000 p0003
  exact p0004

noncomputable def g_n_0ss
    (A : Class) :
    Nominal.NPrf (syn_wss (syn_c0) A) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have p0000 :=
    @g_noel (.cv x)
  have p0001 :=
    @g_pm2_21i (.classMem (.cv x) (syn_c0)) (.classMem (.cv x) A) p0000
  have p0002 :=
    @g_ssriv x (syn_c0) A (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0001
  exact p0002

noncomputable def g_ss0b
    (A : Class) :
    Nominal.NPrf (syn_wb (syn_wss A (syn_c0)) (.classEq A (syn_c0))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_n_0ss A
  have p0001 :=
    @g_eqss A (syn_c0)
  have p0002 :=
    @g_mpbiran2 (.classEq A (syn_c0)) (syn_wss A (syn_c0)) (syn_wss (syn_c0) A) p0000 p0001
  have p0003 :=
    @g_bicomi (.classEq A (syn_c0)) (syn_wss A (syn_c0)) p0002
  exact p0003

noncomputable def g_ss0
    (A : Class) :
    Nominal.NPrf (.imp (syn_wss A (syn_c0)) (.classEq A (syn_c0))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_ss0b A
  have p0001 :=
    @g_biimpi (syn_wss A (syn_c0)) (.classEq A (syn_c0)) p0000
  exact p0001

noncomputable def g_abf
    (ph : Wff) (x : Var) (hyp_abf_1 : Nominal.NPrf (.neg ph)) :
    Nominal.NPrf (.classEq (.cab x ph) (syn_c0)) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var)
  have p0000 :=
    @g_pm2_21i ph (.classMem (.cv x) (syn_c0)) hyp_abf_1
  have p0001 :=
    @g_abssi ph x (syn_c0) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0000
  have p0002 :=
    @g_ss0 (.cab x ph)
  have p0003 :=
    Nominal.mp p0001 p0002
  exact p0003

noncomputable def g_eq0rdv
    (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_ph_x : x ∉ ph.fv) (hyp_eq0rdv_1 : Nominal.NPrf (.imp ph (.neg (.classMem (.cv x) A)))) :
    Nominal.NPrf (.imp ph (.classEq A (syn_c0))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_pm2_21d ph (.classMem (.cv x) A) (.classMem (.cv x) (syn_c0)) hyp_eq0rdv_1
  have p0001 :=
    @g_ssrdv ph x A (syn_c0) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0000
  have p0002 :=
    @g_ss0 A
  have p0003 :=
    @g_syl ph (syn_wss A (syn_c0)) (.classEq A (syn_c0)) p0001 p0002
  exact p0003

noncomputable def g_un00
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wa (.classEq A (syn_c0)) (.classEq B (syn_c0))) (.classEq (syn_cun A B) (syn_c0))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_uneq12 A (syn_c0) B (syn_c0)
  have p0001 :=
    @g_un0 (syn_c0)
  have p0002 :=
    @g_syl6eq (syn_wa (.classEq A (syn_c0)) (.classEq B (syn_c0))) (syn_cun A B) (syn_cun (syn_c0) (syn_c0)) (syn_c0) p0000 p0001
  have p0003 :=
    @g_ssun1 A B
  have p0004 :=
    @g_sseq2 (syn_cun A B) (syn_c0) A
  have p0005 :=
    @g_mpbii (.classEq (syn_cun A B) (syn_c0)) (syn_wss A (syn_cun A B)) (syn_wss A (syn_c0)) p0003 p0004
  have p0006 :=
    @g_ss0b A
  have p0007 :=
    @g_sylib (.classEq (syn_cun A B) (syn_c0)) (syn_wss A (syn_c0)) (.classEq A (syn_c0)) p0005 p0006
  have p0008 :=
    @g_ssun2 B A
  have p0009 :=
    @g_sseq2 (syn_cun A B) (syn_c0) B
  have p0010 :=
    @g_mpbii (.classEq (syn_cun A B) (syn_c0)) (syn_wss B (syn_cun A B)) (syn_wss B (syn_c0)) p0008 p0009
  have p0011 :=
    @g_ss0b B
  have p0012 :=
    @g_sylib (.classEq (syn_cun A B) (syn_c0)) (syn_wss B (syn_c0)) (.classEq B (syn_c0)) p0010 p0011
  have p0013 :=
    @g_jca (.classEq (syn_cun A B) (syn_c0)) (.classEq A (syn_c0)) (.classEq B (syn_c0)) p0007 p0012
  have p0014 :=
    @g_impbii (syn_wa (.classEq A (syn_c0)) (.classEq B (syn_c0))) (.classEq (syn_cun A B) (syn_c0)) p0002 p0013
  exact p0014

noncomputable def g_vss
    (A : Class) :
    Nominal.NPrf (syn_wb (syn_wss (syn_cvv) A) (.classEq A (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_ssv A
  have p0001 :=
    @g_biantrur (syn_wss A (syn_cvv)) (syn_wss (syn_cvv) A) p0000
  have p0002 :=
    @g_eqss A (syn_cvv)
  have p0003 :=
    @g_bitr4i (syn_wss (syn_cvv) A) (syn_wa (syn_wss A (syn_cvv)) (syn_wss (syn_cvv) A)) (.classEq A (syn_cvv)) p0001 p0002
  exact p0003

noncomputable def g_disj
    (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (syn_wb (.classEq (syn_cin A B) (syn_c0)) (syn_wral x A (.neg (.classMem (.cv x) B)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_elin (.cv x) A B
  have p0001 :=
    (by simpa [syn_wb, syn_wa] using (Nominal.biimpRefl (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B))))
  have p0002 :=
    @g_bitr2i (.classMem (.cv x) (syn_cin A B)) (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.neg (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))) p0000 p0001
  have p0003 :=
    @g_con1bii (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) (.classMem (.cv x) (syn_cin A B)) p0002
  have p0004 :=
    @g_albii (.neg (.classMem (.cv x) (syn_cin A B))) (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) x p0003
  have p0005 :=
    @g_eq0 x (syn_cin A B) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0006 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral x A (.neg (.classMem (.cv x) B)))))
  have p0007 :=
    @g_n_3bitr4i (.all x (.neg (.classMem (.cv x) (syn_cin A B)))) (.all x (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))) (.classEq (syn_cin A B) (syn_c0)) (syn_wral x A (.neg (.classMem (.cv x) B))) p0004 p0005 p0006
  exact p0007

noncomputable def g_disjr
    (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (syn_wb (.classEq (syn_cin A B) (syn_c0)) (syn_wral x B (.neg (.classMem (.cv x) A)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_incom A B
  have p0001 :=
    @g_eqeq1i (syn_cin A B) (syn_cin B A) (syn_c0) p0000
  have p0002 :=
    @g_disj x B A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_bitri (.classEq (syn_cin A B) (syn_c0)) (.classEq (syn_cin B A) (syn_c0)) (syn_wral x B (.neg (.classMem (.cv x) A))) p0001 p0002
  exact p0003

noncomputable def g_disj1
    (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (syn_wb (.classEq (syn_cin A B) (syn_c0)) (.all x (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_disj x A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral x A (.neg (.classMem (.cv x) B)))))
  have p0002 :=
    @g_bitri (.classEq (syn_cin A B) (syn_c0)) (syn_wral x A (.neg (.classMem (.cv x) B))) (.all x (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))) p0000 p0001
  exact p0002

noncomputable def g_ssdif0
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wss A B) (.classEq (syn_cdif A B) (syn_c0))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_iman (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 :=
    @g_eldif (.cv x) A B
  have p0002 :=
    @g_xchbinxr (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) (.classMem (.cv x) (syn_cdif A B)) p0000 p0001
  have p0003 :=
    @g_albii (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) (.neg (.classMem (.cv x) (syn_cdif A B))) x p0002
  have p0004 :=
    @g_dfss2 x A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0005 :=
    @g_eq0 x (syn_cdif A B) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0006 :=
    @g_n_3bitr4i (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) (.all x (.neg (.classMem (.cv x) (syn_cdif A B)))) (syn_wss A B) (.classEq (syn_cdif A B) (syn_c0)) p0003 p0004 p0005
  exact p0006

noncomputable def g_inssdif0
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (syn_wb (syn_wss (syn_cin A B) C) (.classEq (syn_cin A (syn_cdif B C)) (syn_c0))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_elin (.cv x) A B
  have p0001 :=
    @g_imbi1i (.classMem (.cv x) (syn_cin A B)) (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C) p0000
  have p0002 :=
    @g_iman (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C)
  have p0003 :=
    @g_bitri (.imp (.classMem (.cv x) (syn_cin A B)) (.classMem (.cv x) C)) (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C)) (.neg (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.neg (.classMem (.cv x) C)))) p0001 p0002
  have p0004 :=
    @g_eldif (.cv x) B C
  have p0005 :=
    @g_anbi2i (.classMem (.cv x) (syn_cdif B C)) (syn_wa (.classMem (.cv x) B) (.neg (.classMem (.cv x) C))) (.classMem (.cv x) A) p0004
  have p0006 :=
    @g_elin (.cv x) A (syn_cdif B C)
  have p0007 :=
    @g_anass (.classMem (.cv x) A) (.classMem (.cv x) B) (.neg (.classMem (.cv x) C))
  have p0008 :=
    @g_n_3bitr4ri (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) (syn_cdif B C))) (syn_wa (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) B) (.neg (.classMem (.cv x) C)))) (.classMem (.cv x) (syn_cin A (syn_cdif B C))) (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.neg (.classMem (.cv x) C))) p0005 p0006 p0007
  have p0009 :=
    @g_xchbinx (.imp (.classMem (.cv x) (syn_cin A B)) (.classMem (.cv x) C)) (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.neg (.classMem (.cv x) C))) (.classMem (.cv x) (syn_cin A (syn_cdif B C))) p0003 p0008
  have p0010 :=
    @g_albii (.imp (.classMem (.cv x) (syn_cin A B)) (.classMem (.cv x) C)) (.neg (.classMem (.cv x) (syn_cin A (syn_cdif B C)))) x p0009
  have p0011 :=
    @g_dfss2 x (syn_cin A B) C (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0012 :=
    @g_eq0 x (syn_cin A (syn_cdif B C)) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0013 :=
    @g_n_3bitr4i (.all x (.imp (.classMem (.cv x) (syn_cin A B)) (.classMem (.cv x) C))) (.all x (.neg (.classMem (.cv x) (syn_cin A (syn_cdif B C))))) (syn_wss (syn_cin A B) C) (.classEq (syn_cin A (syn_cdif B C)) (syn_c0)) p0010 p0011 p0012
  exact p0013

noncomputable def g_difid
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cdif A A) (syn_c0)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_ssid A
  have p0001 :=
    @g_ssdif0 A A
  have p0002 :=
    @g_mpbi (syn_wss A A) (.classEq (syn_cdif A A) (syn_c0)) p0000 p0001
  exact p0002

noncomputable def g_dif0
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cdif A (syn_c0)) A) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_difid A
  have p0001 :=
    @g_difeq2i (syn_cdif A A) (syn_c0) A p0000
  have p0002 :=
    @g_difdif A A
  have p0003 :=
    @g_eqtr3i (syn_cdif A (syn_cdif A A)) (syn_cdif A (syn_c0)) A p0001 p0002
  exact p0003

noncomputable def g_disjdif
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cin A (syn_cdif B A)) (syn_c0)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_inss1 A B
  have p0001 :=
    @g_inssdif0 A B A
  have p0002 :=
    @g_mpbi (syn_wss (syn_cin A B) A) (.classEq (syn_cin A (syn_cdif B A)) (syn_c0)) p0000 p0001
  exact p0002

noncomputable def g_undifv
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cun A (syn_cdif (syn_cvv) A)) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_dfun3 A (syn_cdif (syn_cvv) A)
  have p0001 :=
    @g_disjdif (syn_cdif (syn_cvv) A) (syn_cvv)
  have p0002 :=
    @g_difeq2i (syn_cin (syn_cdif (syn_cvv) A) (syn_cdif (syn_cvv) (syn_cdif (syn_cvv) A))) (syn_c0) (syn_cvv) p0001
  have p0003 :=
    @g_dif0 (syn_cvv)
  have p0004 :=
    @g_n_3eqtri (syn_cun A (syn_cdif (syn_cvv) A)) (syn_cdif (syn_cvv) (syn_cin (syn_cdif (syn_cvv) A) (syn_cdif (syn_cvv) (syn_cdif (syn_cvv) A)))) (syn_cdif (syn_cvv) (syn_c0)) (syn_cvv) p0000 p0002 p0003
  exact p0004

noncomputable def g_undif1
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cun (syn_cdif A B) B) (syn_cun A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_undir A (syn_cdif (syn_cvv) B) B
  have p0001 :=
    @g_invdif A B
  have p0002 :=
    @g_uneq1i (syn_cin A (syn_cdif (syn_cvv) B)) (syn_cdif A B) B p0001
  have p0003 :=
    @g_uncom (syn_cdif (syn_cvv) B) B
  have p0004 :=
    @g_undifv B
  have p0005 :=
    @g_eqtri (syn_cun (syn_cdif (syn_cvv) B) B) (syn_cun B (syn_cdif (syn_cvv) B)) (syn_cvv) p0003 p0004
  have p0006 :=
    @g_ineq2i (syn_cun (syn_cdif (syn_cvv) B) B) (syn_cvv) (syn_cun A B) p0005
  have p0007 :=
    @g_inv1 (syn_cun A B)
  have p0008 :=
    @g_eqtri (syn_cin (syn_cun A B) (syn_cun (syn_cdif (syn_cvv) B) B)) (syn_cin (syn_cun A B) (syn_cvv)) (syn_cun A B) p0006 p0007
  have p0009 :=
    @g_n_3eqtr3i (syn_cun (syn_cin A (syn_cdif (syn_cvv) B)) B) (syn_cin (syn_cun A B) (syn_cun (syn_cdif (syn_cvv) B) B)) (syn_cun (syn_cdif A B) B) (syn_cun A B) p0000 p0002 p0008
  exact p0009

noncomputable def g_undif2
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cun A (syn_cdif B A)) (syn_cun A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_uncom A (syn_cdif B A)
  have p0001 :=
    @g_undif1 B A
  have p0002 :=
    @g_uncom B A
  have p0003 :=
    @g_n_3eqtri (syn_cun A (syn_cdif B A)) (syn_cun (syn_cdif B A) A) (syn_cun B A) (syn_cun A B) p0000 p0001 p0002
  exact p0003

noncomputable def g_inundif
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cun (syn_cin A B) (syn_cdif A B)) A) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_elin (.cv x) A B
  have p0001 :=
    @g_eldif (.cv x) A B
  have p0002 :=
    @g_orbi12i (.classMem (.cv x) (syn_cin A B)) (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) (syn_cdif A B)) (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) p0000 p0001
  have p0003 :=
    @g_pm4_42 (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0004 :=
    @g_bitr4i (syn_wo (.classMem (.cv x) (syn_cin A B)) (.classMem (.cv x) (syn_cdif A B))) (syn_wo (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))) (.classMem (.cv x) A) p0002 p0003
  have p0005 :=
    @g_uneqri x (syn_cin A B) (syn_cdif A B) A (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0004
  exact p0005

noncomputable def g_difun2
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cdif (syn_cun A B) B) (syn_cdif A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_difundir A B B
  have p0001 :=
    @g_difid B
  have p0002 :=
    @g_uneq2i (syn_cdif B B) (syn_c0) (syn_cdif A B) p0001
  have p0003 :=
    @g_un0 (syn_cdif A B)
  have p0004 :=
    @g_n_3eqtri (syn_cdif (syn_cun A B) B) (syn_cun (syn_cdif A B) (syn_cdif B B)) (syn_cun (syn_cdif A B) (syn_c0)) (syn_cdif A B) p0000 p0002 p0003
  exact p0004

noncomputable def g_undif
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wss A B) (.classEq (syn_cun A (syn_cdif B A)) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_ssequn1 A B
  have p0001 :=
    @g_undif2 A B
  have p0002 :=
    @g_eqeq1i (syn_cun A (syn_cdif B A)) (syn_cun A B) B p0001
  have p0003 :=
    @g_bitr4i (syn_wss A B) (.classEq (syn_cun A B) B) (.classEq (syn_cun A (syn_cdif B A)) B) p0000 p0002
  exact p0003

noncomputable def g_ssundif
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (syn_wb (syn_wss A (syn_cun B C)) (syn_wss (syn_cdif A B) C)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_pm5_6 (.classMem (.cv x) A) (.classMem (.cv x) B) (.classMem (.cv x) C)
  have p0001 :=
    @g_eldif (.cv x) A B
  have p0002 :=
    @g_imbi1i (.classMem (.cv x) (syn_cdif A B)) (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) (.classMem (.cv x) C) p0001
  have p0003 :=
    @g_elun (.cv x) B C
  have p0004 :=
    @g_imbi2i (.classMem (.cv x) (syn_cun B C)) (syn_wo (.classMem (.cv x) B) (.classMem (.cv x) C)) (.classMem (.cv x) A) p0003
  have p0005 :=
    @g_n_3bitr4ri (.imp (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) (.classMem (.cv x) C)) (.imp (.classMem (.cv x) A) (syn_wo (.classMem (.cv x) B) (.classMem (.cv x) C))) (.imp (.classMem (.cv x) (syn_cdif A B)) (.classMem (.cv x) C)) (.imp (.classMem (.cv x) A) (.classMem (.cv x) (syn_cun B C))) p0000 p0002 p0004
  have p0006 :=
    @g_albii (.imp (.classMem (.cv x) A) (.classMem (.cv x) (syn_cun B C))) (.imp (.classMem (.cv x) (syn_cdif A B)) (.classMem (.cv x) C)) x p0005
  have p0007 :=
    @g_dfss2 x A (syn_cun B C) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0008 :=
    @g_dfss2 x (syn_cdif A B) C (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0009 :=
    @g_n_3bitr4i (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) (syn_cun B C)))) (.all x (.imp (.classMem (.cv x) (syn_cdif A B)) (.classMem (.cv x) C))) (syn_wss A (syn_cun B C)) (syn_wss (syn_cdif A B) C) p0006 p0007 p0008
  exact p0009

noncomputable def g_r19_2z
    (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wne A (syn_c0)) (syn_wral x A ph)) (syn_wrex x A ph)) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ A.fv
  have p0000 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral x A ph)))
  have p0001 :=
    @g_exintr (.classMem (.cv x) A) ph x
  have p0002 :=
    @g_sylbi (syn_wral x A ph) (.all x (.imp (.classMem (.cv x) A) ph)) (.imp (syn_wex x (.classMem (.cv x) A)) (syn_wex x (syn_wa (.classMem (.cv x) A) ph))) p0000 p0001
  have p0003 :=
    @g_n0 x A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0004 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex x A ph)))
  have p0005 :=
    @g_n_3imtr4g (syn_wral x A ph) (syn_wex x (.classMem (.cv x) A)) (syn_wex x (syn_wa (.classMem (.cv x) A) ph)) (syn_wne A (syn_c0)) (syn_wrex x A ph) p0002 p0003 p0004
  have p0006 :=
    @g_impcom (syn_wral x A ph) (syn_wne A (syn_c0)) (syn_wrex x A ph) p0005
  exact p0006

noncomputable def g_sscon34
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wss A B) (syn_wss (syn_ccompl B) (syn_ccompl A))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_con34b (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 :=
    @g_vex x
  have p0002 :=
    @g_elcompl (.cv x) B p0001
  have p0003 :=
    @g_elcompl (.cv x) A p0001
  have p0004 :=
    @g_imbi12i (.classMem (.cv x) (syn_ccompl B)) (.neg (.classMem (.cv x) B)) (.classMem (.cv x) (syn_ccompl A)) (.neg (.classMem (.cv x) A)) p0002 p0003
  have p0005 :=
    @g_bitr4i (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) (.imp (.neg (.classMem (.cv x) B)) (.neg (.classMem (.cv x) A))) (.imp (.classMem (.cv x) (syn_ccompl B)) (.classMem (.cv x) (syn_ccompl A))) p0000 p0004
  have p0006 :=
    @g_albii (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) (.imp (.classMem (.cv x) (syn_ccompl B)) (.classMem (.cv x) (syn_ccompl A))) x p0005
  have p0007 :=
    @g_dfss2 x A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0008 :=
    @g_dfss2 x (syn_ccompl B) (syn_ccompl A) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0009 :=
    @g_n_3bitr4i (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) (.all x (.imp (.classMem (.cv x) (syn_ccompl B)) (.classMem (.cv x) (syn_ccompl A)))) (syn_wss A B) (syn_wss (syn_ccompl B) (syn_ccompl A)) p0006 p0007 p0008
  exact p0009

noncomputable def g_dfif2
    (ph : Wff) (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (.classEq (syn_cif ph A B) (.cab x (.imp (.imp (.classMem (.cv x) B) ph) (syn_wa (.classMem (.cv x) A) ph)))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_if ph x A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    (by simpa [syn_wb, syn_wo] using (Nominal.biimpRefl (syn_wo (syn_wa (.classMem (.cv x) B) (.neg ph)) (syn_wa (.classMem (.cv x) A) ph))))
  have p0002 :=
    @g_orcom (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) B) (.neg ph))
  have p0003 :=
    @g_iman (.classMem (.cv x) B) ph
  have p0004 :=
    @g_imbi1i (.imp (.classMem (.cv x) B) ph) (.neg (syn_wa (.classMem (.cv x) B) (.neg ph))) (syn_wa (.classMem (.cv x) A) ph) p0003
  have p0005 :=
    @g_n_3bitr4i (syn_wo (syn_wa (.classMem (.cv x) B) (.neg ph)) (syn_wa (.classMem (.cv x) A) ph)) (.imp (.neg (syn_wa (.classMem (.cv x) B) (.neg ph))) (syn_wa (.classMem (.cv x) A) ph)) (syn_wo (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) B) (.neg ph))) (.imp (.imp (.classMem (.cv x) B) ph) (syn_wa (.classMem (.cv x) A) ph)) p0001 p0002 p0004
  have p0006 :=
    @g_abbii (syn_wo (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) B) (.neg ph))) (.imp (.imp (.classMem (.cv x) B) ph) (syn_wa (.classMem (.cv x) A) ph)) x p0005
  have p0007 :=
    @g_eqtri (syn_cif ph A B) (.cab x (syn_wo (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) B) (.neg ph)))) (.cab x (.imp (.imp (.classMem (.cv x) B) ph) (syn_wa (.classMem (.cv x) A) ph))) p0000 p0006
  exact p0007

noncomputable def g_dfif6
    (ph : Wff) (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (.classEq (syn_cif ph A B) (syn_cun (syn_crab x A ph) (syn_crab x B (.neg ph)))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_unab (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) B) (.neg ph)) x
  have p0001 :=
    (by simpa [syn_crab] using (Nominal.classEqRefl (syn_crab x A ph)))
  have p0002 :=
    (by simpa [syn_crab] using (Nominal.classEqRefl (syn_crab x B (.neg ph))))
  have p0003 :=
    @g_uneq12i (syn_crab x A ph) (.cab x (syn_wa (.classMem (.cv x) A) ph)) (syn_crab x B (.neg ph)) (.cab x (syn_wa (.classMem (.cv x) B) (.neg ph))) p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_if ph x A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0005 :=
    @g_n_3eqtr4ri (syn_cun (.cab x (syn_wa (.classMem (.cv x) A) ph)) (.cab x (syn_wa (.classMem (.cv x) B) (.neg ph)))) (.cab x (syn_wo (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) B) (.neg ph)))) (syn_cun (syn_crab x A ph) (syn_crab x B (.neg ph))) (syn_cif ph A B) p0000 p0003 p0004
  exact p0005

noncomputable def g_ifeq1
    (ph : Wff) (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cif ph A C) (syn_cif ph B C))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_rabeq ph x A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_uneq1d (.classEq A B) (syn_crab x A ph) (syn_crab x B ph) (syn_crab x C (.neg ph)) p0000
  have p0002 :=
    @g_dfif6 ph x A C (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_dfif6 ph x B C (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cun (syn_crab x A ph) (syn_crab x C (.neg ph))) (syn_cun (syn_crab x B ph) (syn_crab x C (.neg ph))) (syn_cif ph A C) (syn_cif ph B C) p0001 p0002 p0003
  exact p0004

noncomputable def g_ifeq2
    (ph : Wff) (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cif ph C A) (syn_cif ph C B))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_rabeq (.neg ph) x A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_uneq2d (.classEq A B) (syn_crab x A (.neg ph)) (syn_crab x B (.neg ph)) (syn_crab x C ph) p0000
  have p0002 :=
    @g_dfif6 ph x C A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_dfif6 ph x C B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cun (syn_crab x C ph) (syn_crab x A (.neg ph))) (syn_cun (syn_crab x C ph) (syn_crab x B (.neg ph))) (syn_cif ph C A) (syn_cif ph C B) p0001 p0002 p0003
  exact p0004

noncomputable def g_iftrue
    (ph : Wff) (A : Class) (B : Class) :
    Nominal.NPrf (.imp ph (.classEq (syn_cif ph A B) A)) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_dedlem0a ph (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 :=
    @g_eqabdv ph (.imp (.imp (.classMem (.cv x) B) ph) (syn_wa (.classMem (.cv x) A) ph)) x A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0000
  have p0002 :=
    @g_dfif2 ph x A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_syl6reqr ph A (.cab x (.imp (.imp (.classMem (.cv x) B) ph) (syn_wa (.classMem (.cv x) A) ph))) (syn_cif ph A B) p0001 p0002
  exact p0003

noncomputable def g_iffalse
    (ph : Wff) (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.neg ph) (.classEq (syn_cif ph A B) B)) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_dedlemb ph (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 :=
    @g_eqabdv (.neg ph) (syn_wo (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) B) (.neg ph))) x B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_if ph x A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_syl6reqr (.neg ph) B (.cab x (syn_wo (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) B) (.neg ph)))) (syn_cif ph A B) p0001 p0002
  exact p0003

noncomputable def g_ifeq1d
    (ph : Wff) (ps : Wff) (A : Class) (B : Class) (C : Class) (hyp_ifeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cif ps A C) (syn_cif ps B C))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_ifeq1 ps A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cif ps A C) (syn_cif ps B C)) hyp_ifeq1d_1 p0000
  exact p0001

noncomputable def g_ifeq2d
    (ph : Wff) (ps : Wff) (A : Class) (B : Class) (C : Class) (hyp_ifeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cif ps C A) (syn_cif ps C B))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_ifeq2 ps A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cif ps C A) (syn_cif ps C B)) hyp_ifeq1d_1 p0000
  exact p0001

noncomputable def g_ifeq12d
    (ph : Wff) (ps : Wff) (A : Class) (B : Class) (C : Class) (D : Class) (hyp_ifeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) (hyp_ifeq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cif ps A C) (syn_cif ps B D))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_ifeq1d ph ps A B C hyp_ifeq1d_1
  have p0001 :=
    @g_ifeq2d ph ps C D B hyp_ifeq12d_2
  have p0002 :=
    @g_eqtrd ph (syn_cif ps A C) (syn_cif ps B C) (syn_cif ps B D) p0000 p0001
  exact p0002

noncomputable def g_ifbi
    (ph : Wff) (ps : Wff) (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wb ph ps) (.classEq (syn_cif ph A B) (syn_cif ps A B))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_dfbi3 ph ps
  have p0001 :=
    @g_iftrue ph A B
  have p0002 :=
    @g_iftrue ps A B
  have p0003 :=
    @g_eqcomd ps (syn_cif ps A B) A p0002
  have p0004 :=
    @g_sylan9eq ph ps (syn_cif ph A B) A (syn_cif ps A B) p0001 p0003
  have p0005 :=
    @g_iffalse ph A B
  have p0006 :=
    @g_iffalse ps A B
  have p0007 :=
    @g_eqcomd (.neg ps) (syn_cif ps A B) B p0006
  have p0008 :=
    @g_sylan9eq (.neg ph) (.neg ps) (syn_cif ph A B) B (syn_cif ps A B) p0005 p0007
  have p0009 :=
    @g_jaoi (syn_wa ph ps) (.classEq (syn_cif ph A B) (syn_cif ps A B)) (syn_wa (.neg ph) (.neg ps)) p0004 p0008
  have p0010 :=
    @g_sylbi (syn_wb ph ps) (syn_wo (syn_wa ph ps) (syn_wa (.neg ph) (.neg ps))) (.classEq (syn_cif ph A B) (syn_cif ps A B)) p0000 p0009
  exact p0010

noncomputable def g_ifbid
    (ph : Wff) (ps : Wff) (ch : Wff) (A : Class) (B : Class) (hyp_ifbid_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cif ps A B) (syn_cif ch A B))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_ifbi ps ch A B
  have p0001 :=
    @g_syl ph (syn_wb ps ch) (.classEq (syn_cif ps A B) (syn_cif ch A B)) hyp_ifbid_1 p0000
  exact p0001

noncomputable def g_ifbieq2d
    (ph : Wff) (ps : Wff) (ch : Wff) (A : Class) (B : Class) (C : Class) (hyp_ifbieq2d_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) (hyp_ifbieq2d_2 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cif ps C A) (syn_cif ch C B))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_ifbid ph ps ch C A hyp_ifbieq2d_1
  have p0001 :=
    @g_ifeq2d ph ch A B C hyp_ifbieq2d_2
  have p0002 :=
    @g_eqtrd ph (syn_cif ps C A) (syn_cif ch C A) (syn_cif ch C B) p0000 p0001
  exact p0002

noncomputable def g_ifbieq12d
    (ph : Wff) (ps : Wff) (ch : Wff) (A : Class) (B : Class) (C : Class) (D : Class) (hyp_ifbieq12d_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) (hyp_ifbieq12d_2 : Nominal.NPrf (.imp ph (.classEq A C))) (hyp_ifbieq12d_3 : Nominal.NPrf (.imp ph (.classEq B D))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cif ps A B) (syn_cif ch C D))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_ifbid ph ps ch A B hyp_ifbieq12d_1
  have p0001 :=
    @g_ifeq12d ph ch A C B D hyp_ifbieq12d_2 hyp_ifbieq12d_3
  have p0002 :=
    @g_eqtrd ph (syn_cif ps A B) (syn_cif ch A B) (syn_cif ch C D) p0000 p0001
  exact p0002

noncomputable def g_ifclda
    (ph : Wff) (ps : Wff) (A : Class) (B : Class) (C : Class) (hyp_ifclda_1 : Nominal.NPrf (.imp (syn_wa ph ps) (.classMem A C))) (hyp_ifclda_2 : Nominal.NPrf (.imp (syn_wa ph (.neg ps)) (.classMem B C))) :
    Nominal.NPrf (.imp ph (.classMem (syn_cif ps A B) C)) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_iftrue ps A B
  have p0001 :=
    @g_adantl ps (.classEq (syn_cif ps A B) A) ph p0000
  have p0002 :=
    @g_eqeltrd (syn_wa ph ps) (syn_cif ps A B) A C p0001 hyp_ifclda_1
  have p0003 :=
    @g_iffalse ps A B
  have p0004 :=
    @g_adantl (.neg ps) (.classEq (syn_cif ps A B) B) ph p0003
  have p0005 :=
    @g_eqeltrd (syn_wa ph (.neg ps)) (syn_cif ps A B) B C p0004 hyp_ifclda_2
  have p0006 :=
    @g_pm2_61dan ph ps (.classMem (syn_cif ps A B) C) p0002 p0005
  exact p0006

noncomputable def g_elimif
    (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (A : Class) (B : Class) (hyp_elimif_1 : Nominal.NPrf (.imp (.classEq (syn_cif ph A B) A) (syn_wb ps ch))) (hyp_elimif_2 : Nominal.NPrf (.imp (.classEq (syn_cif ph A B) B) (syn_wb ps th))) :
    Nominal.NPrf (syn_wb ps (syn_wo (syn_wa ph ch) (syn_wa (.neg ph) th))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ th.fv ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_exmid ph
  have p0001 :=
    @g_biantrur (syn_wo ph (.neg ph)) ps p0000
  have p0002 :=
    @g_andir ph (.neg ph) ps
  have p0003 :=
    @g_iftrue ph A B
  have p0004 :=
    @g_syl ph (.classEq (syn_cif ph A B) A) (syn_wb ps ch) p0003 hyp_elimif_1
  have p0005 :=
    @g_pm5_32i ph ps ch p0004
  have p0006 :=
    @g_iffalse ph A B
  have p0007 :=
    @g_syl (.neg ph) (.classEq (syn_cif ph A B) B) (syn_wb ps th) p0006 hyp_elimif_2
  have p0008 :=
    @g_pm5_32i (.neg ph) ps th p0007
  have p0009 :=
    @g_orbi12i (syn_wa ph ps) (syn_wa ph ch) (syn_wa (.neg ph) ps) (syn_wa (.neg ph) th) p0005 p0008
  have p0010 :=
    @g_n_3bitri ps (syn_wa (syn_wo ph (.neg ph)) ps) (syn_wo (syn_wa ph ps) (syn_wa (.neg ph) ps)) (syn_wo (syn_wa ph ch) (syn_wa (.neg ph) th)) p0001 p0002 p0009
  exact p0010

noncomputable def g_ifbothda
    (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (et : Wff) (A : Class) (B : Class) (hyp_ifboth_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A B)) (syn_wb ps th))) (hyp_ifboth_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ph A B)) (syn_wb ch th))) (hyp_ifbothda_3 : Nominal.NPrf (.imp (syn_wa et ph) ps)) (hyp_ifbothda_4 : Nominal.NPrf (.imp (syn_wa et (.neg ph)) ch)) :
    Nominal.NPrf (.imp et th) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ th.fv ∪ et.fv ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_iftrue ph A B
  have p0001 :=
    @g_eqcomd ph (syn_cif ph A B) A p0000
  have p0002 :=
    @g_syl ph (.classEq A (syn_cif ph A B)) (syn_wb ps th) p0001 hyp_ifboth_1
  have p0003 :=
    @g_adantl ph (syn_wb ps th) et p0002
  have p0004 :=
    @g_mpbid (syn_wa et ph) ps th hyp_ifbothda_3 p0003
  have p0005 :=
    @g_iffalse ph A B
  have p0006 :=
    @g_eqcomd (.neg ph) (syn_cif ph A B) B p0005
  have p0007 :=
    @g_syl (.neg ph) (.classEq B (syn_cif ph A B)) (syn_wb ch th) p0006 hyp_ifboth_2
  have p0008 :=
    @g_adantl (.neg ph) (syn_wb ch th) et p0007
  have p0009 :=
    @g_mpbid (syn_wa et (.neg ph)) ch th hyp_ifbothda_4 p0008
  have p0010 :=
    @g_pm2_61dan et ph th p0004 p0009
  exact p0010

noncomputable def g_ifboth
    (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (A : Class) (B : Class) (hyp_ifboth_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A B)) (syn_wb ps th))) (hyp_ifboth_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ph A B)) (syn_wb ch th))) :
    Nominal.NPrf (.imp (syn_wa ps ch) th) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ th.fv ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_simpll ps ch ph
  have p0001 :=
    @g_simplr ps ch (.neg ph)
  have p0002 :=
    @g_ifbothda ph ps ch th (syn_wa ps ch) A B hyp_ifboth_1 hyp_ifboth_2 p0000 p0001
  exact p0002

noncomputable def g_elif
    (ph : Wff) (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cif ph B C)) (syn_wo (syn_wa ph (.classMem A B)) (syn_wa (.neg ph) (.classMem A C)))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_eleq2 (syn_cif ph B C) B A
  have p0001 :=
    @g_eleq2 (syn_cif ph B C) C A
  have p0002 :=
    @g_elimif ph (.classMem A (syn_cif ph B C)) (.classMem A B) (.classMem A C) B C p0000 p0001
  exact p0002

noncomputable def g_ifcl
    (ph : Wff) (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A C) (.classMem B C)) (.classMem (syn_cif ph A B) C)) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_eleq1 A (syn_cif ph A B) C
  have p0001 :=
    @g_eleq1 B (syn_cif ph A B) C
  have p0002 :=
    @g_ifboth ph (.classMem A C) (.classMem B C) (.classMem (syn_cif ph A B) C) A B p0000 p0001
  exact p0002

noncomputable def g_ifeqor
    (ph : Wff) (A : Class) (B : Class) :
    Nominal.NPrf (syn_wo (.classEq (syn_cif ph A B) A) (.classEq (syn_cif ph A B) B)) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_iftrue ph A B
  have p0001 :=
    @g_con3i ph (.classEq (syn_cif ph A B) A) p0000
  have p0002 :=
    @g_iffalse ph A B
  have p0003 :=
    @g_syl (.neg (.classEq (syn_cif ph A B) A)) (.neg ph) (.classEq (syn_cif ph A B) B) p0001 p0002
  have p0004 :=
    @g_orri (.classEq (syn_cif ph A B) A) (.classEq (syn_cif ph A B) B) p0003
  exact p0004

noncomputable def g_dedth
    (ph : Wff) (ps : Wff) (ch : Wff) (A : Class) (B : Class) (hyp_dedth_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A B)) (syn_wb ps ch))) (hyp_dedth_2 : Nominal.NPrf ch) :
    Nominal.NPrf (.imp ph ps) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_iftrue ph A B
  have p0001 :=
    @g_eqcomd ph (syn_cif ph A B) A p0000
  have p0002 :=
    @g_syl ph (.classEq A (syn_cif ph A B)) (syn_wb ps ch) p0001 hyp_dedth_1
  have p0003 :=
    @g_mpbiri ph ps ch hyp_dedth_2 p0002
  exact p0003

noncomputable def g_dedth2h
    (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) (A : Class) (B : Class) (C : Class) (D : Class) (hyp_dedth2h_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A C)) (syn_wb ch th))) (hyp_dedth2h_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ps B D)) (syn_wb th ta))) (hyp_dedth2h_3 : Nominal.NPrf ta) :
    Nominal.NPrf (.imp (syn_wa ph ps) ch) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ th.fv ∪ ta.fv ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_imbi2d (.classEq A (syn_cif ph A C)) ch th ps hyp_dedth2h_1
  have p0001 :=
    @g_dedth ps th ta B D hyp_dedth2h_2 hyp_dedth2h_3
  have p0002 :=
    @g_dedth ph (.imp ps ch) (.imp ps th) A C p0000 p0001
  have p0003 :=
    @g_imp ph ps ch p0002
  exact p0003

noncomputable def g_dedth3h
    (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) (et : Wff) (ze : Wff) (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (S : Class) (hyp_dedth3h_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A D)) (syn_wb th ta))) (hyp_dedth3h_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ps B R)) (syn_wb ta et))) (hyp_dedth3h_3 : Nominal.NPrf (.imp (.classEq C (syn_cif ch C S)) (syn_wb et ze))) (hyp_dedth3h_4 : Nominal.NPrf ze) :
    Nominal.NPrf (.imp (syn_w3a ph ps ch) th) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ th.fv ∪ ta.fv ∪ et.fv ∪ ze.fv ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ S.fv
  have p0000 :=
    @g_imbi2d (.classEq A (syn_cif ph A D)) th ta (syn_wa ps ch) hyp_dedth3h_1
  have p0001 :=
    @g_dedth2h ps ch ta et ze B C R S hyp_dedth3h_2 hyp_dedth3h_3 hyp_dedth3h_4
  have p0002 :=
    @g_dedth ph (.imp (syn_wa ps ch) th) (.imp (syn_wa ps ch) ta) A D p0000 p0001
  have p0003 :=
    @g_n_3impib ph ps ch th p0002
  exact p0003

noncomputable def g_dedth4h
    (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) (et : Wff) (ze : Wff) (si : Wff) (rh : Wff) (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (S : Class) (F : Class) (G : Class) (hyp_dedth4h_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A R)) (syn_wb ta et))) (hyp_dedth4h_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ps B S)) (syn_wb et ze))) (hyp_dedth4h_3 : Nominal.NPrf (.imp (.classEq C (syn_cif ch C F)) (syn_wb ze si))) (hyp_dedth4h_4 : Nominal.NPrf (.imp (.classEq D (syn_cif th D G)) (syn_wb si rh))) (hyp_dedth4h_5 : Nominal.NPrf rh) :
    Nominal.NPrf (.imp (syn_wa (syn_wa ph ps) (syn_wa ch th)) ta) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ th.fv ∪ ta.fv ∪ et.fv ∪ ze.fv ∪ si.fv ∪ rh.fv ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ S.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_imbi2d (.classEq A (syn_cif ph A R)) ta et (syn_wa ch th) hyp_dedth4h_1
  have p0001 :=
    @g_imbi2d (.classEq B (syn_cif ps B S)) et ze (syn_wa ch th) hyp_dedth4h_2
  have p0002 :=
    @g_dedth2h ch th ze si rh C D F G hyp_dedth4h_3 hyp_dedth4h_4 hyp_dedth4h_5
  have p0003 :=
    @g_dedth2h ph ps (.imp (syn_wa ch th) ta) (.imp (syn_wa ch th) et) (.imp (syn_wa ch th) ze) A B R S p0000 p0001 p0002
  have p0004 :=
    @g_imp (syn_wa ph ps) (syn_wa ch th) ta p0003
  exact p0004

noncomputable def g_dedth2v
    (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (A : Class) (B : Class) (C : Class) (D : Class) (hyp_dedth2v_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A C)) (syn_wb ps ch))) (hyp_dedth2v_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ph B D)) (syn_wb ch th))) (hyp_dedth2v_3 : Nominal.NPrf th) :
    Nominal.NPrf (.imp ph ps) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ th.fv ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_dedth2h ph ph ps ch th A B C D hyp_dedth2v_1 hyp_dedth2v_2 hyp_dedth2v_3
  have p0001 :=
    @g_anidms ph ps p0000
  exact p0001

noncomputable def g_dedth3v
    (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (S : Class) (hyp_dedth3v_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A D)) (syn_wb ps ch))) (hyp_dedth3v_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ph B R)) (syn_wb ch th))) (hyp_dedth3v_3 : Nominal.NPrf (.imp (.classEq C (syn_cif ph C S)) (syn_wb th ta))) (hyp_dedth3v_4 : Nominal.NPrf ta) :
    Nominal.NPrf (.imp ph ps) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ th.fv ∪ ta.fv ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ S.fv
  have p0000 :=
    @g_dedth3h ph ph ph ps ch th ta A B C D R S hyp_dedth3v_1 hyp_dedth3v_2 hyp_dedth3v_3 hyp_dedth3v_4
  have p0001 :=
    @g_n_3anidm12 ph ph ps p0000
  have p0002 :=
    @g_anidms ph ps p0001
  exact p0002

noncomputable def g_dedth4v
    (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) (et : Wff) (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (S : Class) (T : Class) (U : Class) (hyp_dedth4v_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A R)) (syn_wb ps ch))) (hyp_dedth4v_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ph B S)) (syn_wb ch th))) (hyp_dedth4v_3 : Nominal.NPrf (.imp (.classEq C (syn_cif ph C T)) (syn_wb th ta))) (hyp_dedth4v_4 : Nominal.NPrf (.imp (.classEq D (syn_cif ph D U)) (syn_wb ta et))) (hyp_dedth4v_5 : Nominal.NPrf et) :
    Nominal.NPrf (.imp ph ps) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ th.fv ∪ ta.fv ∪ et.fv ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ S.fv ∪ T.fv ∪ U.fv
  have p0000 :=
    @g_dedth4h ph ph ph ph ps ch th ta et A B C D R S T U hyp_dedth4v_1 hyp_dedth4v_2 hyp_dedth4v_3 hyp_dedth4v_4 hyp_dedth4v_5
  have p0001 :=
    @g_anidms (syn_wa ph ph) ps p0000
  have p0002 :=
    @g_anidms ph ps p0001
  exact p0002

noncomputable def g_elimhyp2v
    (ph : Wff) (ch : Wff) (th : Wff) (ta : Wff) (et : Wff) (A : Class) (B : Class) (C : Class) (D : Class) (hyp_elimhyp2v_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A C)) (syn_wb ph ch))) (hyp_elimhyp2v_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ph B D)) (syn_wb ch th))) (hyp_elimhyp2v_3 : Nominal.NPrf (.imp (.classEq C (syn_cif ph A C)) (syn_wb ta et))) (hyp_elimhyp2v_4 : Nominal.NPrf (.imp (.classEq D (syn_cif ph B D)) (syn_wb et th))) (hyp_elimhyp2v_5 : Nominal.NPrf ta) :
    Nominal.NPrf th := by
  let proofSupport : Finset Var := ph.fv ∪ ch.fv ∪ th.fv ∪ ta.fv ∪ et.fv ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_iftrue ph A C
  have p0001 :=
    @g_eqcomd ph (syn_cif ph A C) A p0000
  have p0002 :=
    @g_syl ph (.classEq A (syn_cif ph A C)) (syn_wb ph ch) p0001 hyp_elimhyp2v_1
  have p0003 :=
    @g_iftrue ph B D
  have p0004 :=
    @g_eqcomd ph (syn_cif ph B D) B p0003
  have p0005 :=
    @g_syl ph (.classEq B (syn_cif ph B D)) (syn_wb ch th) p0004 hyp_elimhyp2v_2
  have p0006 :=
    @g_bitrd ph ph ch th p0002 p0005
  have p0007 :=
    @g_ibi ph th p0006
  have p0008 :=
    @g_iffalse ph A C
  have p0009 :=
    @g_eqcomd (.neg ph) (syn_cif ph A C) C p0008
  have p0010 :=
    @g_syl (.neg ph) (.classEq C (syn_cif ph A C)) (syn_wb ta et) p0009 hyp_elimhyp2v_3
  have p0011 :=
    @g_iffalse ph B D
  have p0012 :=
    @g_eqcomd (.neg ph) (syn_cif ph B D) D p0011
  have p0013 :=
    @g_syl (.neg ph) (.classEq D (syn_cif ph B D)) (syn_wb et th) p0012 hyp_elimhyp2v_4
  have p0014 :=
    @g_bitrd (.neg ph) ta et th p0010 p0013
  have p0015 :=
    @g_mpbii (.neg ph) ta th hyp_elimhyp2v_5 p0014
  have p0016 :=
    @g_pm2_61i ph th p0007 p0015
  exact p0016

noncomputable def g_elimhyp3v
    (ph : Wff) (ch : Wff) (th : Wff) (ta : Wff) (et : Wff) (ze : Wff) (si : Wff) (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (S : Class) (hyp_elimhyp3v_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A D)) (syn_wb ph ch))) (hyp_elimhyp3v_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ph B R)) (syn_wb ch th))) (hyp_elimhyp3v_3 : Nominal.NPrf (.imp (.classEq C (syn_cif ph C S)) (syn_wb th ta))) (hyp_elimhyp3v_4 : Nominal.NPrf (.imp (.classEq D (syn_cif ph A D)) (syn_wb et ze))) (hyp_elimhyp3v_5 : Nominal.NPrf (.imp (.classEq R (syn_cif ph B R)) (syn_wb ze si))) (hyp_elimhyp3v_6 : Nominal.NPrf (.imp (.classEq S (syn_cif ph C S)) (syn_wb si ta))) (hyp_elimhyp3v_7 : Nominal.NPrf et) :
    Nominal.NPrf ta := by
  let proofSupport : Finset Var := ph.fv ∪ ch.fv ∪ th.fv ∪ ta.fv ∪ et.fv ∪ ze.fv ∪ si.fv ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ S.fv
  have p0000 :=
    @g_iftrue ph A D
  have p0001 :=
    @g_eqcomd ph (syn_cif ph A D) A p0000
  have p0002 :=
    @g_syl ph (.classEq A (syn_cif ph A D)) (syn_wb ph ch) p0001 hyp_elimhyp3v_1
  have p0003 :=
    @g_iftrue ph B R
  have p0004 :=
    @g_eqcomd ph (syn_cif ph B R) B p0003
  have p0005 :=
    @g_syl ph (.classEq B (syn_cif ph B R)) (syn_wb ch th) p0004 hyp_elimhyp3v_2
  have p0006 :=
    @g_iftrue ph C S
  have p0007 :=
    @g_eqcomd ph (syn_cif ph C S) C p0006
  have p0008 :=
    @g_syl ph (.classEq C (syn_cif ph C S)) (syn_wb th ta) p0007 hyp_elimhyp3v_3
  have p0009 :=
    @g_n_3bitrd ph ph ch th ta p0002 p0005 p0008
  have p0010 :=
    @g_ibi ph ta p0009
  have p0011 :=
    @g_iffalse ph A D
  have p0012 :=
    @g_eqcomd (.neg ph) (syn_cif ph A D) D p0011
  have p0013 :=
    @g_syl (.neg ph) (.classEq D (syn_cif ph A D)) (syn_wb et ze) p0012 hyp_elimhyp3v_4
  have p0014 :=
    @g_iffalse ph B R
  have p0015 :=
    @g_eqcomd (.neg ph) (syn_cif ph B R) R p0014
  have p0016 :=
    @g_syl (.neg ph) (.classEq R (syn_cif ph B R)) (syn_wb ze si) p0015 hyp_elimhyp3v_5
  have p0017 :=
    @g_iffalse ph C S
  have p0018 :=
    @g_eqcomd (.neg ph) (syn_cif ph C S) S p0017
  have p0019 :=
    @g_syl (.neg ph) (.classEq S (syn_cif ph C S)) (syn_wb si ta) p0018 hyp_elimhyp3v_6
  have p0020 :=
    @g_n_3bitrd (.neg ph) et ze si ta p0013 p0016 p0019
  have p0021 :=
    @g_mpbii (.neg ph) et ta hyp_elimhyp3v_7 p0020
  have p0022 :=
    @g_pm2_61i ph ta p0010 p0021
  exact p0022

noncomputable def g_elimhyp4v
    (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) (et : Wff) (ze : Wff) (si : Wff) (rh : Wff) (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (S : Class) (F : Class) (G : Class) (hyp_elimhyp4v_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A D)) (syn_wb ph ch))) (hyp_elimhyp4v_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ph B R)) (syn_wb ch th))) (hyp_elimhyp4v_3 : Nominal.NPrf (.imp (.classEq C (syn_cif ph C S)) (syn_wb th ta))) (hyp_elimhyp4v_4 : Nominal.NPrf (.imp (.classEq F (syn_cif ph F G)) (syn_wb ta ps))) (hyp_elimhyp4v_5 : Nominal.NPrf (.imp (.classEq D (syn_cif ph A D)) (syn_wb et ze))) (hyp_elimhyp4v_6 : Nominal.NPrf (.imp (.classEq R (syn_cif ph B R)) (syn_wb ze si))) (hyp_elimhyp4v_7 : Nominal.NPrf (.imp (.classEq S (syn_cif ph C S)) (syn_wb si rh))) (hyp_elimhyp4v_8 : Nominal.NPrf (.imp (.classEq G (syn_cif ph F G)) (syn_wb rh ps))) (hyp_elimhyp4v_9 : Nominal.NPrf et) :
    Nominal.NPrf ps := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ th.fv ∪ ta.fv ∪ et.fv ∪ ze.fv ∪ si.fv ∪ rh.fv ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ S.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_iftrue ph A D
  have p0001 :=
    @g_eqcomd ph (syn_cif ph A D) A p0000
  have p0002 :=
    @g_syl ph (.classEq A (syn_cif ph A D)) (syn_wb ph ch) p0001 hyp_elimhyp4v_1
  have p0003 :=
    @g_iftrue ph B R
  have p0004 :=
    @g_eqcomd ph (syn_cif ph B R) B p0003
  have p0005 :=
    @g_syl ph (.classEq B (syn_cif ph B R)) (syn_wb ch th) p0004 hyp_elimhyp4v_2
  have p0006 :=
    @g_bitrd ph ph ch th p0002 p0005
  have p0007 :=
    @g_iftrue ph C S
  have p0008 :=
    @g_eqcomd ph (syn_cif ph C S) C p0007
  have p0009 :=
    @g_syl ph (.classEq C (syn_cif ph C S)) (syn_wb th ta) p0008 hyp_elimhyp4v_3
  have p0010 :=
    @g_iftrue ph F G
  have p0011 :=
    @g_eqcomd ph (syn_cif ph F G) F p0010
  have p0012 :=
    @g_syl ph (.classEq F (syn_cif ph F G)) (syn_wb ta ps) p0011 hyp_elimhyp4v_4
  have p0013 :=
    @g_n_3bitrd ph ph th ta ps p0006 p0009 p0012
  have p0014 :=
    @g_ibi ph ps p0013
  have p0015 :=
    @g_iffalse ph A D
  have p0016 :=
    @g_eqcomd (.neg ph) (syn_cif ph A D) D p0015
  have p0017 :=
    @g_syl (.neg ph) (.classEq D (syn_cif ph A D)) (syn_wb et ze) p0016 hyp_elimhyp4v_5
  have p0018 :=
    @g_iffalse ph B R
  have p0019 :=
    @g_eqcomd (.neg ph) (syn_cif ph B R) R p0018
  have p0020 :=
    @g_syl (.neg ph) (.classEq R (syn_cif ph B R)) (syn_wb ze si) p0019 hyp_elimhyp4v_6
  have p0021 :=
    @g_bitrd (.neg ph) et ze si p0017 p0020
  have p0022 :=
    @g_iffalse ph C S
  have p0023 :=
    @g_eqcomd (.neg ph) (syn_cif ph C S) S p0022
  have p0024 :=
    @g_syl (.neg ph) (.classEq S (syn_cif ph C S)) (syn_wb si rh) p0023 hyp_elimhyp4v_7
  have p0025 :=
    @g_iffalse ph F G
  have p0026 :=
    @g_eqcomd (.neg ph) (syn_cif ph F G) G p0025
  have p0027 :=
    @g_syl (.neg ph) (.classEq G (syn_cif ph F G)) (syn_wb rh ps) p0026 hyp_elimhyp4v_8
  have p0028 :=
    @g_n_3bitrd (.neg ph) et si rh ps p0021 p0024 p0027
  have p0029 :=
    @g_mpbii (.neg ph) et ps hyp_elimhyp4v_9 p0028
  have p0030 :=
    @g_pm2_61i ph ps p0014 p0029
  exact p0030

noncomputable def g_keephyp
    (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (A : Class) (B : Class) (hyp_keephyp_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A B)) (syn_wb ps th))) (hyp_keephyp_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ph A B)) (syn_wb ch th))) (hyp_keephyp_3 : Nominal.NPrf ps) (hyp_keephyp_4 : Nominal.NPrf ch) :
    Nominal.NPrf th := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ th.fv ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_ifboth ph ps ch th A B hyp_keephyp_1 hyp_keephyp_2
  have p0001 :=
    @g_mp2an ps ch th hyp_keephyp_3 hyp_keephyp_4 p0000
  exact p0001

noncomputable def g_keephyp2v
    (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) (et : Wff) (A : Class) (B : Class) (C : Class) (D : Class) (hyp_keephyp2v_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A C)) (syn_wb ps ch))) (hyp_keephyp2v_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ph B D)) (syn_wb ch th))) (hyp_keephyp2v_3 : Nominal.NPrf (.imp (.classEq C (syn_cif ph A C)) (syn_wb ta et))) (hyp_keephyp2v_4 : Nominal.NPrf (.imp (.classEq D (syn_cif ph B D)) (syn_wb et th))) (hyp_keephyp2v_5 : Nominal.NPrf ps) (hyp_keephyp2v_6 : Nominal.NPrf ta) :
    Nominal.NPrf th := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ th.fv ∪ ta.fv ∪ et.fv ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_iftrue ph A C
  have p0001 :=
    @g_eqcomd ph (syn_cif ph A C) A p0000
  have p0002 :=
    @g_syl ph (.classEq A (syn_cif ph A C)) (syn_wb ps ch) p0001 hyp_keephyp2v_1
  have p0003 :=
    @g_iftrue ph B D
  have p0004 :=
    @g_eqcomd ph (syn_cif ph B D) B p0003
  have p0005 :=
    @g_syl ph (.classEq B (syn_cif ph B D)) (syn_wb ch th) p0004 hyp_keephyp2v_2
  have p0006 :=
    @g_bitrd ph ps ch th p0002 p0005
  have p0007 :=
    @g_mpbii ph ps th hyp_keephyp2v_5 p0006
  have p0008 :=
    @g_iffalse ph A C
  have p0009 :=
    @g_eqcomd (.neg ph) (syn_cif ph A C) C p0008
  have p0010 :=
    @g_syl (.neg ph) (.classEq C (syn_cif ph A C)) (syn_wb ta et) p0009 hyp_keephyp2v_3
  have p0011 :=
    @g_iffalse ph B D
  have p0012 :=
    @g_eqcomd (.neg ph) (syn_cif ph B D) D p0011
  have p0013 :=
    @g_syl (.neg ph) (.classEq D (syn_cif ph B D)) (syn_wb et th) p0012 hyp_keephyp2v_4
  have p0014 :=
    @g_bitrd (.neg ph) ta et th p0010 p0013
  have p0015 :=
    @g_mpbii (.neg ph) ta th hyp_keephyp2v_6 p0014
  have p0016 :=
    @g_pm2_61i ph th p0007 p0015
  exact p0016

noncomputable def g_keepel
    (ph : Wff) (A : Class) (B : Class) (C : Class) (hyp_keepel_1 : Nominal.NPrf (.classMem A C)) (hyp_keepel_2 : Nominal.NPrf (.classMem B C)) :
    Nominal.NPrf (.classMem (syn_cif ph A B) C) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_eleq1 A (syn_cif ph A B) C
  have p0001 :=
    @g_eleq1 B (syn_cif ph A B) C
  have p0002 :=
    @g_keephyp ph (.classMem A C) (.classMem B C) (.classMem (syn_cif ph A B) C) A B p0000 p0001 hyp_keepel_1 hyp_keepel_2
  exact p0002

noncomputable def g_ifex
    (ph : Wff) (A : Class) (B : Class) (hyp_dedex_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_dedex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cif ph A B) (syn_cvv)) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_keepel ph A B (syn_cvv) hyp_dedex_1 hyp_dedex_2
  exact p0000

noncomputable def g_pweq
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cpw A) (syn_cpw B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_sseq2 A B (.cv x)
  have p0001 :=
    @g_abbidv (.classEq A B) (syn_wss (.cv x) A) (syn_wss (.cv x) B) x (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw x A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw x B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (.cab x (syn_wss (.cv x) A)) (.cab x (syn_wss (.cv x) B)) (syn_cpw A) (syn_cpw B) p0001 p0002 p0003
  exact p0004

noncomputable def g_pweqi
    (A : Class) (B : Class) (hyp_pweqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cpw A) (syn_cpw B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_pweq A B
  have p0001 :=
    Nominal.mp hyp_pweqi_1 p0000
  exact p0001

noncomputable def g_pweqd
    (ph : Wff) (A : Class) (B : Class) (hyp_pweqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cpw A) (syn_cpw B))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_pweq A B
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cpw A) (syn_cpw B)) hyp_pweqd_1 p0000
  exact p0001

noncomputable def g_elpw
    (A : Class) (B : Class) (hyp_elpw_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cpw B)) (syn_wss A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_sseq1 (.cv x) A B
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw x B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0002 :=
    @g_elab2 (syn_wss (.cv x) B) (syn_wss A B) x A (syn_cpw B) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) hyp_elpw_1 p0000 p0001
  exact p0002

noncomputable def g_elpwg
    (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (syn_wb (.classMem A (syn_cpw B)) (syn_wss A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_eleq1 (.cv x) A (syn_cpw B)
  have p0001 :=
    @g_sseq1 (.cv x) A B
  have p0002 :=
    @g_vex x
  have p0003 :=
    @g_elpw (.cv x) B p0002
  have p0004 :=
    @g_vtoclbg (.classMem (.cv x) (syn_cpw B)) (syn_wss (.cv x) B) (.classMem A (syn_cpw B)) (syn_wss A B) x A V (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0000 p0001 p0003
  exact p0004

noncomputable def g_sneq
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_csn A) (syn_csn B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_eqeq2 A B (.cv x)
  have p0001 :=
    @g_abbidv (.classEq A B) (.classEq (.cv x) A) (.classEq (.cv x) B) x (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn x A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn x B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (.cab x (.classEq (.cv x) A)) (.cab x (.classEq (.cv x) B)) (syn_csn A) (syn_csn B) p0001 p0002 p0003
  exact p0004

noncomputable def g_sneqi
    (A : Class) (B : Class) (hyp_sneqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_csn A) (syn_csn B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_sneq A B
  have p0001 :=
    Nominal.mp hyp_sneqi_1 p0000
  exact p0001

noncomputable def g_sneqd
    (ph : Wff) (A : Class) (B : Class) (hyp_sneqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_csn A) (syn_csn B))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_sneq A B
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_csn A) (syn_csn B)) hyp_sneqd_1 p0000
  exact p0001

noncomputable def g_dfsn2
    (A : Class) :
    Nominal.NPrf (.classEq (syn_csn A) (syn_cpr A A)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_cpr] using (Nominal.classEqRefl (syn_cpr A A)))
  have p0001 :=
    @g_unidm (syn_csn A)
  have p0002 :=
    @g_eqtr2i (syn_cpr A A) (syn_cun (syn_csn A) (syn_csn A)) (syn_csn A) p0000 p0001
  exact p0002

noncomputable def g_elsn
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_csn A)) (.classEq (.cv x) A)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn x A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_eqabri (.classEq (.cv x) A) x (syn_csn A) p0000
  exact p0001

noncomputable def g_dfpr2
    (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (.classEq (syn_cpr A B) (.cab x (syn_wo (.classEq (.cv x) A) (.classEq (.cv x) B)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    (by simpa [syn_cpr] using (Nominal.classEqRefl (syn_cpr A B)))
  have p0001 :=
    @g_elun (.cv x) (syn_csn A) (syn_csn B)
  have p0002 :=
    @g_elsn x A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_elsn x B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0004 :=
    @g_orbi12i (.classMem (.cv x) (syn_csn A)) (.classEq (.cv x) A) (.classMem (.cv x) (syn_csn B)) (.classEq (.cv x) B) p0002 p0003
  have p0005 :=
    @g_bitri (.classMem (.cv x) (syn_cun (syn_csn A) (syn_csn B))) (syn_wo (.classMem (.cv x) (syn_csn A)) (.classMem (.cv x) (syn_csn B))) (syn_wo (.classEq (.cv x) A) (.classEq (.cv x) B)) p0001 p0004
  have p0006 :=
    @g_eqabi (syn_wo (.classEq (.cv x) A) (.classEq (.cv x) B)) x (syn_cun (syn_csn A) (syn_csn B)) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0005
  have p0007 :=
    @g_eqtri (syn_cpr A B) (syn_cun (syn_csn A) (syn_csn B)) (.cab x (syn_wo (.classEq (.cv x) A) (.classEq (.cv x) B))) p0000 p0006
  exact p0007

noncomputable def g_elprg
    (A : Class) (B : Class) (C : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (syn_wb (.classMem A (syn_cpr B C)) (syn_wo (.classEq A B) (.classEq A C)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_eqeq1 (.cv x) A B
  have p0001 :=
    @g_eqeq1 (.cv x) A C
  have p0002 :=
    @g_orbi12d (.classEq (.cv x) A) (.classEq (.cv x) B) (.classEq A B) (.classEq (.cv x) C) (.classEq A C) p0000 p0001
  have p0003 :=
    @g_dfpr2 x B C (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0004 :=
    @g_elab2g (syn_wo (.classEq (.cv x) B) (.classEq (.cv x) C)) (syn_wo (.classEq A B) (.classEq A C)) x A (syn_cpr B C) V (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0002 p0003
  exact p0004

noncomputable def g_elpr
    (A : Class) (B : Class) (C : Class) (hyp_elpr_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cpr B C)) (syn_wo (.classEq A B) (.classEq A C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_elprg A B C (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_elpr_1 p0000
  exact p0001

noncomputable def g_elpr2
    (A : Class) (B : Class) (C : Class) (hyp_elpr2_1 : Nominal.NPrf (.classMem B (syn_cvv))) (hyp_elpr2_2 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cpr B C)) (syn_wo (.classEq A B) (.classEq A C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_elprg A B C (syn_cpr B C)
  have p0001 :=
    @g_ibi (.classMem A (syn_cpr B C)) (syn_wo (.classEq A B) (.classEq A C)) p0000
  have p0002 :=
    @g_eleq1 A B (syn_cvv)
  have p0003 :=
    @g_mpbiri (.classEq A B) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) hyp_elpr2_1 p0002
  have p0004 :=
    @g_eleq1 A C (syn_cvv)
  have p0005 :=
    @g_mpbiri (.classEq A C) (.classMem A (syn_cvv)) (.classMem C (syn_cvv)) hyp_elpr2_2 p0004
  have p0006 :=
    @g_jaoi (.classEq A B) (.classMem A (syn_cvv)) (.classEq A C) p0003 p0005
  have p0007 :=
    @g_elprg A B C (syn_cvv)
  have p0008 :=
    @g_syl (syn_wo (.classEq A B) (.classEq A C)) (.classMem A (syn_cvv)) (syn_wb (.classMem A (syn_cpr B C)) (syn_wo (.classEq A B) (.classEq A C))) p0006 p0007
  have p0009 :=
    @g_ibir (syn_wo (.classEq A B) (.classEq A C)) (.classMem A (syn_cpr B C)) p0008
  have p0010 :=
    @g_impbii (.classMem A (syn_cpr B C)) (syn_wo (.classEq A B) (.classEq A C)) p0001 p0009
  exact p0010

noncomputable def g_elsncg
    (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (syn_wb (.classMem A (syn_csn B)) (.classEq A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_eqeq1 (.cv x) A B
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn x B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0002 :=
    @g_elab2g (.classEq (.cv x) B) (.classEq A B) x A (syn_csn B) V (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0000 p0001
  exact p0002

noncomputable def g_elsnc
    (A : Class) (B : Class) (hyp_elsnc_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem A (syn_csn B)) (.classEq A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_elsncg A B (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_elsnc_1 p0000
  exact p0001

noncomputable def g_elsni
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_csn B)) (.classEq A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_elsncg A B (syn_csn B)
  have p0001 :=
    @g_ibi (.classMem A (syn_csn B)) (.classEq A B) p0000
  exact p0001

noncomputable def g_snidg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem A (syn_csn A))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  have p0000 :=
    @g_eqid A
  have p0001 :=
    @g_elsncg A A V
  have p0002 :=
    @g_mpbiri (.classMem A V) (.classMem A (syn_csn A)) (.classEq A A) p0000 p0001
  exact p0002

noncomputable def g_snidb
    (A : Class) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cvv)) (.classMem A (syn_csn A))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_snidg A (syn_cvv)
  have p0001 :=
    @g_elex A (syn_csn A)
  have p0002 :=
    @g_impbii (.classMem A (syn_cvv)) (.classMem A (syn_csn A)) p0000 p0001
  exact p0002

noncomputable def g_snid
    (A : Class) (hyp_snid_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem A (syn_csn A)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_snidb A
  have p0001 :=
    @g_mpbi (.classMem A (syn_cvv)) (.classMem A (syn_csn A)) hyp_snid_1 p0000
  exact p0001

noncomputable def g_elsnc2g
    (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem B V) (syn_wb (.classMem A (syn_csn B)) (.classEq A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv
  have p0000 :=
    @g_elsni A B
  have p0001 :=
    @g_snidg B V
  have p0002 :=
    @g_eleq1 A B (syn_csn B)
  have p0003 :=
    @g_syl5ibrcom (.classMem B V) (.classMem A (syn_csn B)) (.classEq A B) (.classMem B (syn_csn B)) p0001 p0002
  have p0004 :=
    @g_impbid2 (.classMem B V) (.classMem A (syn_csn B)) (.classEq A B) p0000 p0003
  exact p0004

noncomputable def g_elsnc2
    (A : Class) (B : Class) (hyp_elsnc2_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem A (syn_csn B)) (.classEq A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_elsnc2g A B (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_elsnc2_1 p0000
  exact p0001

noncomputable def g_rexsns
    (ph : Wff) (x : Var) (A : Class) (V : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.imp (.classMem A V) (syn_wb (syn_wrex x (syn_csn A) ph) (syn_wsbc A x ph))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 :=
    @g_sbc5 ph x A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_a1i (syn_wb (syn_wsbc A x ph) (syn_wex x (syn_wa (.classEq (.cv x) A) ph))) (.classMem A V) p0000
  have p0002 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex x (syn_csn A) ph)))
  have p0003 :=
    @g_elsn x A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0004 :=
    @g_anbi1i (.classMem (.cv x) (syn_csn A)) (.classEq (.cv x) A) ph p0003
  have p0005 :=
    @g_exbii (syn_wa (.classMem (.cv x) (syn_csn A)) ph) (syn_wa (.classEq (.cv x) A) ph) x p0004
  have p0006 :=
    @g_bitri (syn_wrex x (syn_csn A) ph) (syn_wex x (syn_wa (.classMem (.cv x) (syn_csn A)) ph)) (syn_wex x (syn_wa (.classEq (.cv x) A) ph)) p0002 p0005
  have p0007 :=
    @g_syl6rbbr (.classMem A V) (syn_wsbc A x ph) (syn_wex x (syn_wa (.classEq (.cv x) A) ph)) (syn_wrex x (syn_csn A) ph) p0001 p0006
  exact p0007

noncomputable def g_rexsng
    (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class) (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv) (hyp_ralsng_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (.classMem A V) (syn_wb (syn_wrex x (syn_csn A) ph) ps)) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({x} : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 :=
    @g_rexsns ph x A V (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_sbcieg ph ps x A V (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) hyp_ralsng_1
  have p0002 :=
    @g_bitrd (.classMem A V) (syn_wrex x (syn_csn A) ph) (syn_wsbc A x ph) ps p0000 p0001
  exact p0002

noncomputable def g_rexsn
    (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv) (hyp_ralsn_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_ralsn_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (syn_wrex x (syn_csn A) ph) ps) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({x} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_rexsng ph ps x A (syn_cvv) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) hyp_ralsn_2
  have p0001 :=
    Nominal.mp hyp_ralsn_1 p0000
  exact p0001

noncomputable def g_disjsn
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (.classEq (syn_cin A (syn_csn B)) (syn_c0)) (.neg (.classMem B A))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_disj1 x A (syn_csn B) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_con2b (.classMem (.cv x) A) (.classMem (.cv x) (syn_csn B))
  have p0002 :=
    @g_elsn x B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_imbi1i (.classMem (.cv x) (syn_csn B)) (.classEq (.cv x) B) (.neg (.classMem (.cv x) A)) p0002
  have p0004 :=
    @g_imnan (.classEq (.cv x) B) (.classMem (.cv x) A)
  have p0005 :=
    @g_n_3bitri (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) (syn_csn B)))) (.imp (.classMem (.cv x) (syn_csn B)) (.neg (.classMem (.cv x) A))) (.imp (.classEq (.cv x) B) (.neg (.classMem (.cv x) A))) (.neg (syn_wa (.classEq (.cv x) B) (.classMem (.cv x) A))) p0001 p0003 p0004
  have p0006 :=
    @g_albii (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) (syn_csn B)))) (.neg (syn_wa (.classEq (.cv x) B) (.classMem (.cv x) A))) x p0005
  have p0007 :=
    @g_alnex (syn_wa (.classEq (.cv x) B) (.classMem (.cv x) A)) x
  have p0008 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClelGoal, syn_wb, syn_wex, syn_wa, Wff.biimp, Wff.ex, Wff.conj, Wff.neg] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x B A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)))
  have p0009 :=
    @g_xchbinxr (.all x (.neg (syn_wa (.classEq (.cv x) B) (.classMem (.cv x) A)))) (syn_wex x (syn_wa (.classEq (.cv x) B) (.classMem (.cv x) A))) (.classMem B A) p0007 p0008
  have p0010 :=
    @g_n_3bitri (.classEq (syn_cin A (syn_csn B)) (syn_c0)) (.all x (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) (syn_csn B))))) (.all x (.neg (syn_wa (.classEq (.cv x) B) (.classMem (.cv x) A)))) (.neg (.classMem B A)) p0000 p0006 p0009
  exact p0010

noncomputable def g_snprc
    (A : Class) :
    Nominal.NPrf (syn_wb (.neg (.classMem A (syn_cvv))) (.classEq (syn_csn A) (syn_c0))) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have p0000 :=
    @g_elsn x A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_exbii (.classMem (.cv x) (syn_csn A)) (.classEq (.cv x) A) x p0000
  have p0002 :=
    @g_neq0 x (syn_csn A) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_isset x A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0004 :=
    @g_n_3bitr4i (syn_wex x (.classMem (.cv x) (syn_csn A))) (syn_wex x (.classEq (.cv x) A)) (.neg (.classEq (syn_csn A) (syn_c0))) (.classMem A (syn_cvv)) p0001 p0002 p0003
  have p0005 :=
    @g_con1bii (.classEq (syn_csn A) (syn_c0)) (.classMem A (syn_cvv)) p0004
  exact p0005

noncomputable def g_rabsn
    (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (.imp (.classMem B A) (.classEq (syn_crab x A (.classEq (.cv x) B)) (syn_csn B))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_eleq1 (.cv x) B A
  have p0001 :=
    @g_pm5_32ri (.classEq (.cv x) B) (.classMem (.cv x) A) (.classMem B A) p0000
  have p0002 :=
    @g_baib (syn_wa (.classMem (.cv x) A) (.classEq (.cv x) B)) (.classMem B A) (.classEq (.cv x) B) p0001
  have p0003 :=
    @g_abbidv (.classMem B A) (syn_wa (.classMem (.cv x) A) (.classEq (.cv x) B)) (.classEq (.cv x) B) x (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0002
  have p0004 :=
    (by simpa [syn_crab] using (Nominal.classEqRefl (syn_crab x A (.classEq (.cv x) B))))
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn x B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0006 :=
    @g_n_3eqtr4g (.classMem B A) (.cab x (syn_wa (.classMem (.cv x) A) (.classEq (.cv x) B))) (.cab x (.classEq (.cv x) B)) (syn_crab x A (.classEq (.cv x) B)) (syn_csn B) p0003 p0004 p0005
  exact p0006

noncomputable def g_prcom
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cpr A B) (syn_cpr B A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_uncom (syn_csn A) (syn_csn B)
  have p0001 :=
    (by simpa [syn_cpr] using (Nominal.classEqRefl (syn_cpr A B)))
  have p0002 :=
    (by simpa [syn_cpr] using (Nominal.classEqRefl (syn_cpr B A)))
  have p0003 :=
    @g_n_3eqtr4i (syn_cun (syn_csn A) (syn_csn B)) (syn_cun (syn_csn B) (syn_csn A)) (syn_cpr A B) (syn_cpr B A) p0000 p0001 p0002
  exact p0003

noncomputable def g_preq1
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cpr A C) (syn_cpr B C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_sneq A B
  have p0001 :=
    @g_uneq1d (.classEq A B) (syn_csn A) (syn_csn B) (syn_csn C) p0000
  have p0002 :=
    (by simpa [syn_cpr] using (Nominal.classEqRefl (syn_cpr A C)))
  have p0003 :=
    (by simpa [syn_cpr] using (Nominal.classEqRefl (syn_cpr B C)))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cun (syn_csn A) (syn_csn C)) (syn_cun (syn_csn B) (syn_csn C)) (syn_cpr A C) (syn_cpr B C) p0001 p0002 p0003
  exact p0004

noncomputable def g_preq2
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cpr C A) (syn_cpr C B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_preq1 A B C
  have p0001 :=
    @g_prcom C A
  have p0002 :=
    @g_prcom C B
  have p0003 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cpr A C) (syn_cpr B C) (syn_cpr C A) (syn_cpr C B) p0000 p0001 p0002
  exact p0003

noncomputable def g_preq12
    (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf (.imp (syn_wa (.classEq A C) (.classEq B D)) (.classEq (syn_cpr A B) (syn_cpr C D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_preq1 A C B
  have p0001 :=
    @g_preq2 B D C
  have p0002 :=
    @g_sylan9eq (.classEq A C) (.classEq B D) (syn_cpr A B) (syn_cpr C B) (syn_cpr C D) p0000 p0001
  exact p0002

noncomputable def g_preq2d
    (ph : Wff) (A : Class) (B : Class) (C : Class) (hyp_preq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cpr C A) (syn_cpr C B))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_preq2 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cpr C A) (syn_cpr C B)) hyp_preq1d_1 p0000
  exact p0001

noncomputable def g_preq12d
    (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class) (hyp_preq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) (hyp_preq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cpr A C) (syn_cpr B D))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_preq12 A C B D
  have p0001 :=
    @g_syl2anc ph (.classEq A B) (.classEq C D) (.classEq (syn_cpr A C) (syn_cpr B D)) hyp_preq1d_1 hyp_preq12d_2 p0000
  exact p0001

noncomputable def g_prid1g
    (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem A (syn_cpr A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv
  have p0000 :=
    @g_eqid A
  have p0001 :=
    @g_orci (.classEq A A) (.classEq A B) p0000
  have p0002 :=
    @g_elprg A A B V
  have p0003 :=
    @g_mpbiri (.classMem A V) (.classMem A (syn_cpr A B)) (syn_wo (.classEq A A) (.classEq A B)) p0001 p0002
  exact p0003

noncomputable def g_prid1
    (A : Class) (B : Class) (hyp_prid1_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem A (syn_cpr A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_prid1g A B (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_prid1_1 p0000
  exact p0001

noncomputable def g_snnzg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (syn_wne (syn_csn A) (syn_c0))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  have p0000 :=
    @g_snidg A V
  have p0001 :=
    @g_ne0i (syn_csn A) A
  have p0002 :=
    @g_syl (.classMem A V) (.classMem A (syn_csn A)) (syn_wne (syn_csn A) (syn_c0)) p0000 p0001
  exact p0002

noncomputable def g_snnz
    (A : Class) (hyp_snnz_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wne (syn_csn A) (syn_c0)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_snnzg A (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_snnz_1 p0000
  exact p0001

noncomputable def g_snss
    (A : Class) (B : Class) (hyp_snss_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem A B) (syn_wss (syn_csn A) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_elsn x A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_imbi1i (.classMem (.cv x) (syn_csn A)) (.classEq (.cv x) A) (.classMem (.cv x) B) p0000
  have p0002 :=
    @g_albii (.imp (.classMem (.cv x) (syn_csn A)) (.classMem (.cv x) B)) (.imp (.classEq (.cv x) A) (.classMem (.cv x) B)) x p0001
  have p0003 :=
    @g_dfss2 x (syn_csn A) B (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0004 :=
    @g_clel2 x A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) hyp_snss_1
  have p0005 :=
    @g_n_3bitr4ri (.all x (.imp (.classMem (.cv x) (syn_csn A)) (.classMem (.cv x) B))) (.all x (.imp (.classEq (.cv x) A) (.classMem (.cv x) B))) (syn_wss (syn_csn A) B) (.classMem A B) p0002 p0003 p0004
  exact p0005

noncomputable def g_eldifsn
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cdif B (syn_csn C))) (syn_wa (.classMem A B) (syn_wne A C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_eldif A B (syn_csn C)
  have p0001 :=
    @g_elsncg A C B
  have p0002 :=
    @g_necon3bbid (.classMem A B) (.classMem A (syn_csn C)) A C p0001
  have p0003 :=
    @g_pm5_32i (.classMem A B) (.neg (.classMem A (syn_csn C))) (syn_wne A C) p0002
  have p0004 :=
    @g_bitri (.classMem A (syn_cdif B (syn_csn C))) (syn_wa (.classMem A B) (.neg (.classMem A (syn_csn C)))) (syn_wa (.classMem A B) (syn_wne A C)) p0000 p0003
  exact p0004

noncomputable def g_eldifsni
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cdif B (syn_csn C))) (syn_wne A C)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_eldifsn A B C
  have p0001 :=
    @g_simprbi (.classMem A (syn_cdif B (syn_csn C))) (.classMem A B) (syn_wne A C) p0000
  exact p0001

noncomputable def g_neldifsn
    (A : Class) (B : Class) :
    Nominal.NPrf (.neg (.classMem A (syn_cdif B (syn_csn A)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_neirr A
  have p0001 :=
    @g_eldifsni A B A
  have p0002 :=
    @g_mto (.classMem A (syn_cdif B (syn_csn A))) (syn_wne A A) p0000 p0001
  exact p0002

noncomputable def g_snssg
    (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (syn_wb (.classMem A B) (syn_wss (syn_csn A) B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_eleq1 (.cv x) A B
  have p0001 :=
    @g_sneq (.cv x) A
  have p0002 :=
    @g_sseq1d (.classEq (.cv x) A) (syn_csn (.cv x)) (syn_csn A) B p0001
  have p0003 :=
    @g_vex x
  have p0004 :=
    @g_snss (.cv x) B p0003
  have p0005 :=
    @g_vtoclbg (.classMem (.cv x) B) (syn_wss (syn_csn (.cv x)) B) (.classMem A B) (syn_wss (syn_csn A) B) x A V (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0000 p0002 p0004
  exact p0005

noncomputable def g_difsn
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.neg (.classMem A B)) (.classEq (syn_cdif B (syn_csn A)) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_eldifsn (.cv x) B A
  have p0001 :=
    @g_simpl (.classMem (.cv x) B) (syn_wne (.cv x) A)
  have p0002 :=
    @g_eleq1 (.cv x) A B
  have p0003 :=
    @g_biimpcd (.classEq (.cv x) A) (.classMem (.cv x) B) (.classMem A B) p0002
  have p0004 :=
    @g_necon3bd (.classMem (.cv x) B) (.classMem A B) (.cv x) A p0003
  have p0005 :=
    @g_com12 (.classMem (.cv x) B) (.neg (.classMem A B)) (syn_wne (.cv x) A) p0004
  have p0006 :=
    @g_ancld (.neg (.classMem A B)) (.classMem (.cv x) B) (syn_wne (.cv x) A) p0005
  have p0007 :=
    @g_impbid2 (.neg (.classMem A B)) (syn_wa (.classMem (.cv x) B) (syn_wne (.cv x) A)) (.classMem (.cv x) B) p0001 p0006
  have p0008 :=
    @g_syl5bb (.classMem (.cv x) (syn_cdif B (syn_csn A))) (syn_wa (.classMem (.cv x) B) (syn_wne (.cv x) A)) (.neg (.classMem A B)) (.classMem (.cv x) B) p0000 p0007
  have p0009 :=
    @g_eqrdv (.neg (.classMem A B)) x (syn_cdif B (syn_csn A)) B (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0008
  exact p0009

noncomputable def g_snssi
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem A B) (syn_wss (syn_csn A) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_snssg A B B
  have p0001 :=
    @g_ibi (.classMem A B) (syn_wss (syn_csn A) B) p0000
  exact p0001

noncomputable def g_snssd
    (ph : Wff) (A : Class) (B : Class) (hyp_snssd_1 : Nominal.NPrf (.imp ph (.classMem A B))) :
    Nominal.NPrf (.imp ph (syn_wss (syn_csn A) B)) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_snssg A B B
  have p0001 :=
    @g_syl ph (.classMem A B) (syn_wb (.classMem A B) (syn_wss (syn_csn A) B)) hyp_snssd_1 p0000
  have p0002 :=
    @g_mpbid ph (.classMem A B) (syn_wss (syn_csn A) B) hyp_snssd_1 p0001
  exact p0002

noncomputable def g_difsnid
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem B A) (.classEq (syn_cun (syn_cdif A (syn_csn B)) (syn_csn B)) A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_uncom (syn_cdif A (syn_csn B)) (syn_csn B)
  have p0001 :=
    @g_snssi B A
  have p0002 :=
    @g_undif (syn_csn B) A
  have p0003 :=
    @g_sylib (.classMem B A) (syn_wss (syn_csn B) A) (.classEq (syn_cun (syn_csn B) (syn_cdif A (syn_csn B))) A) p0001 p0002
  have p0004 :=
    @g_syl5eq (.classMem B A) (syn_cun (syn_cdif A (syn_csn B)) (syn_csn B)) (syn_cun (syn_csn B) (syn_cdif A (syn_csn B))) A p0000 p0003
  exact p0004

noncomputable def g_sssn
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wss A (syn_csn B)) (syn_wo (.classEq A (syn_c0)) (.classEq A (syn_csn B)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_neq0 x A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_ssel A (syn_csn B) (.cv x)
  have p0002 :=
    @g_elsni (.cv x) B
  have p0003 :=
    @g_syl6 (syn_wss A (syn_csn B)) (.classMem (.cv x) A) (.classMem (.cv x) (syn_csn B)) (.classEq (.cv x) B) p0001 p0002
  have p0004 :=
    @g_eleq1 (.cv x) B A
  have p0005 :=
    @g_syl6 (syn_wss A (syn_csn B)) (.classMem (.cv x) A) (.classEq (.cv x) B) (syn_wb (.classMem (.cv x) A) (.classMem B A)) p0003 p0004
  have p0006 :=
    @g_ibd (syn_wss A (syn_csn B)) (.classMem (.cv x) A) (.classMem B A) p0005
  have p0007 :=
    @g_exlimdv (syn_wss A (syn_csn B)) (.classMem (.cv x) A) (.classMem B A) x (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0006
  have p0008 :=
    @g_syl5bi (.neg (.classEq A (syn_c0))) (syn_wex x (.classMem (.cv x) A)) (syn_wss A (syn_csn B)) (.classMem B A) p0000 p0007
  have p0009 :=
    @g_snssi B A
  have p0010 :=
    @g_syl6 (syn_wss A (syn_csn B)) (.neg (.classEq A (syn_c0))) (.classMem B A) (syn_wss (syn_csn B) A) p0008 p0009
  have p0011 :=
    @g_anc2li (syn_wss A (syn_csn B)) (.neg (.classEq A (syn_c0))) (syn_wss (syn_csn B) A) p0010
  have p0012 :=
    @g_eqss A (syn_csn B)
  have p0013 :=
    @g_syl6ibr (syn_wss A (syn_csn B)) (.neg (.classEq A (syn_c0))) (syn_wa (syn_wss A (syn_csn B)) (syn_wss (syn_csn B) A)) (.classEq A (syn_csn B)) p0011 p0012
  have p0014 :=
    @g_orrd (syn_wss A (syn_csn B)) (.classEq A (syn_c0)) (.classEq A (syn_csn B)) p0013
  have p0015 :=
    @g_n_0ss (syn_csn B)
  have p0016 :=
    @g_sseq1 A (syn_c0) (syn_csn B)
  have p0017 :=
    @g_mpbiri (.classEq A (syn_c0)) (syn_wss A (syn_csn B)) (syn_wss (syn_c0) (syn_csn B)) p0015 p0016
  have p0018 :=
    @g_eqimss A (syn_csn B)
  have p0019 :=
    @g_jaoi (.classEq A (syn_c0)) (syn_wss A (syn_csn B)) (.classEq A (syn_csn B)) p0017 p0018
  have p0020 :=
    @g_impbii (syn_wss A (syn_csn B)) (syn_wo (.classEq A (syn_c0)) (.classEq A (syn_csn B))) p0014 p0019
  exact p0020

noncomputable def g_sneqr
    (A : Class) (B : Class) (hyp_sneqr_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.classEq (syn_csn A) (syn_csn B)) (.classEq A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_snid A hyp_sneqr_1
  have p0001 :=
    @g_eleq2 (syn_csn A) (syn_csn B) A
  have p0002 :=
    @g_mpbii (.classEq (syn_csn A) (syn_csn B)) (.classMem A (syn_csn A)) (.classMem A (syn_csn B)) p0000 p0001
  have p0003 :=
    @g_elsnc A B hyp_sneqr_1
  have p0004 :=
    @g_sylib (.classEq (syn_csn A) (syn_csn B)) (.classMem A (syn_csn B)) (.classEq A B) p0002 p0003
  exact p0004

noncomputable def g_sneqrg
    (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.imp (.classEq (syn_csn A) (syn_csn B)) (.classEq A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_sneq (.cv x) A
  have p0001 :=
    @g_eqeq1d (.classEq (.cv x) A) (syn_csn (.cv x)) (syn_csn A) (syn_csn B) p0000
  have p0002 :=
    @g_eqeq1 (.cv x) A B
  have p0003 :=
    @g_imbi12d (.classEq (.cv x) A) (.classEq (syn_csn (.cv x)) (syn_csn B)) (.classEq (syn_csn A) (syn_csn B)) (.classEq (.cv x) B) (.classEq A B) p0001 p0002
  have p0004 :=
    @g_vex x
  have p0005 :=
    @g_sneqr (.cv x) B p0004
  have p0006 :=
    @g_vtoclg (.imp (.classEq (syn_csn (.cv x)) (syn_csn B)) (.classEq (.cv x) B)) (.imp (.classEq (syn_csn A) (syn_csn B)) (.classEq A B)) x A V (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0003 p0005
  exact p0006

noncomputable def g_sneqbg
    (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (syn_wb (.classEq (syn_csn A) (syn_csn B)) (.classEq A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv
  have p0000 :=
    @g_sneqrg A B V
  have p0001 :=
    @g_sneq A B
  have p0002 :=
    @g_impbid1 (.classMem A V) (.classEq (syn_csn A) (syn_csn B)) (.classEq A B) p0000 p0001
  exact p0002

noncomputable def g_sneqb
    (A : Class) (B : Class) (hyp_sneqb_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classEq (syn_csn A) (syn_csn B)) (.classEq A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_sneqbg A B (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_sneqb_1 p0000
  exact p0001

noncomputable def g_pwv
     :
    Nominal.NPrf (.classEq (syn_cpw (syn_cvv)) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have p0000 :=
    @g_ssv (.cv x)
  have p0001 :=
    @g_vex x
  have p0002 :=
    @g_elpw (.cv x) (syn_cvv) p0001
  have p0003 :=
    @g_mpbir (.classMem (.cv x) (syn_cpw (syn_cvv))) (syn_wss (.cv x) (syn_cvv)) p0000 p0002
  have p0004 :=
    @g_n_2th (.classMem (.cv x) (syn_cpw (syn_cvv))) (.classMem (.cv x) (syn_cvv)) p0003 p0001
  have p0005 :=
    @g_eqriv x (syn_cpw (syn_cvv)) (syn_cvv) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0004
  exact p0005

noncomputable def g_unsneqsn
    (A : Class) (B : Class) (C : Class) (hyp_unsneqsn_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (.classEq (syn_cun A (syn_csn B)) (syn_csn C)) (syn_wo (.classEq A (syn_c0)) (.classEq A (syn_csn B)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_ssun2 (syn_csn B) A
  have p0001 :=
    @g_snid B hyp_unsneqsn_1
  have p0002 :=
    @g_sselii (syn_csn B) (syn_cun A (syn_csn B)) B p0000 p0001
  have p0003 :=
    @g_eleq2 (syn_cun A (syn_csn B)) (syn_csn C) B
  have p0004 :=
    @g_mpbii (.classEq (syn_cun A (syn_csn B)) (syn_csn C)) (.classMem B (syn_cun A (syn_csn B))) (.classMem B (syn_csn C)) p0002 p0003
  have p0005 :=
    @g_elsni B C
  have p0006 :=
    @g_syl (.classEq (syn_cun A (syn_csn B)) (syn_csn C)) (.classMem B (syn_csn C)) (.classEq B C) p0004 p0005
  have p0007 :=
    @g_sneq B C
  have p0008 :=
    @g_eqeq2d (.classEq B C) (syn_csn B) (syn_csn C) (syn_cun A (syn_csn B)) p0007
  have p0009 :=
    @g_biimprd (.classEq B C) (.classEq (syn_cun A (syn_csn B)) (syn_csn B)) (.classEq (syn_cun A (syn_csn B)) (syn_csn C)) p0008
  have p0010 :=
    @g_mpcom (.classEq B C) (.classEq (syn_cun A (syn_csn B)) (syn_csn C)) (.classEq (syn_cun A (syn_csn B)) (syn_csn B)) p0006 p0009
  have p0011 :=
    @g_ssequn1 A (syn_csn B)
  have p0012 :=
    @g_sylibr (.classEq (syn_cun A (syn_csn B)) (syn_csn C)) (.classEq (syn_cun A (syn_csn B)) (syn_csn B)) (syn_wss A (syn_csn B)) p0010 p0011
  have p0013 :=
    @g_sssn A B
  have p0014 :=
    @g_sylib (.classEq (syn_cun A (syn_csn B)) (syn_csn C)) (syn_wss A (syn_csn B)) (syn_wo (.classEq A (syn_c0)) (.classEq A (syn_csn B))) p0012 p0013
  exact p0014

noncomputable def g_dfpss4
    (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (syn_wb (syn_wpss A B) (syn_wa (syn_wss A B) (syn_wrex x B (.neg (.classMem (.cv x) A))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_dfpss3 A B
  have p0001 :=
    @g_dfss3 x B A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0002 :=
    @g_dfral2 (.classMem (.cv x) A) x B
  have p0003 :=
    @g_bitr2i (syn_wss B A) (syn_wral x B (.classMem (.cv x) A)) (.neg (syn_wrex x B (.neg (.classMem (.cv x) A)))) p0001 p0002
  have p0004 :=
    @g_con1bii (syn_wrex x B (.neg (.classMem (.cv x) A))) (syn_wss B A) p0003
  have p0005 :=
    @g_anbi2i (.neg (syn_wss B A)) (syn_wrex x B (.neg (.classMem (.cv x) A))) (syn_wss A B) p0004
  have p0006 :=
    @g_bitri (syn_wpss A B) (syn_wa (syn_wss A B) (.neg (syn_wss B A))) (syn_wa (syn_wss A B) (syn_wrex x B (.neg (.classMem (.cv x) A)))) p0000 p0005
  exact p0006

noncomputable def g_adj11
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wa (.neg (.classMem C A)) (.neg (.classMem C B))) (syn_wb (.classEq (syn_cun A (syn_csn C)) (syn_cun B (syn_csn C))) (.classEq A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_difeq1 (syn_cun A (syn_csn C)) (syn_cun B (syn_csn C)) (syn_csn C)
  have p0001 :=
    @g_difun2 A (syn_csn C)
  have p0002 :=
    @g_difun2 B (syn_csn C)
  have p0003 :=
    @g_n_3eqtr3g (.classEq (syn_cun A (syn_csn C)) (syn_cun B (syn_csn C))) (syn_cdif (syn_cun A (syn_csn C)) (syn_csn C)) (syn_cdif (syn_cun B (syn_csn C)) (syn_csn C)) (syn_cdif A (syn_csn C)) (syn_cdif B (syn_csn C)) p0000 p0001 p0002
  have p0004 :=
    @g_difsn C A
  have p0005 :=
    @g_difsn C B
  have p0006 :=
    @g_eqeqan12d (.neg (.classMem C A)) (.neg (.classMem C B)) (syn_cdif A (syn_csn C)) A (syn_cdif B (syn_csn C)) B p0004 p0005
  have p0007 :=
    @g_syl5ib (.classEq (syn_cun A (syn_csn C)) (syn_cun B (syn_csn C))) (.classEq (syn_cdif A (syn_csn C)) (syn_cdif B (syn_csn C))) (syn_wa (.neg (.classMem C A)) (.neg (.classMem C B))) (.classEq A B) p0003 p0006
  have p0008 :=
    @g_uneq1 A B (syn_csn C)
  have p0009 :=
    @g_impbid1 (syn_wa (.neg (.classMem C A)) (.neg (.classMem C B))) (.classEq (syn_cun A (syn_csn C)) (syn_cun B (syn_csn C))) (.classEq A B) p0007 p0008
  exact p0009

noncomputable def g_dfuni2
    (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_cuni A) (.cab x (syn_wrex y A (.classMem (.cv x) (.cv y))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_uni x y A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_exancom (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A) y
  have p0002 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y A (.classMem (.cv x) (.cv y)))))
  have p0003 :=
    @g_bitr4i (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A))) (syn_wex y (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) (.cv y)))) (syn_wrex y A (.classMem (.cv x) (.cv y))) p0001 p0002
  have p0004 :=
    @g_abbii (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A))) (syn_wrex y A (.classMem (.cv x) (.cv y))) x p0003
  have p0005_e00_recanon : Nominal.NPrf (.classEq (syn_cuni A) (.cab x (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cuni syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        ·
          exact Nominal.RecanonTransportDev.TRecanonClass.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonClass.cab
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0000
  have p0005 :=
    @g_eqtri (syn_cuni A) (.cab x (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A)))) (.cab x (syn_wrex y A (.classMem (.cv x) (.cv y)))) p0005_e00_recanon p0004
  exact p0005

noncomputable def g_eluni
    (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cuni B)) (syn_wex x (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) B)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_elex A (syn_cuni B)
  have p0001 :=
    @g_elex A (.cv x)
  have p0002 :=
    @g_adantr (.classMem A (.cv x)) (.classMem A (syn_cvv)) (.classMem (.cv x) B) p0001
  have p0003 :=
    @g_exlimiv (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) B)) (.classMem A (syn_cvv)) x (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0002
  have p0004 :=
    @g_eleq1 (.cv y) A (.cv x)
  have p0005 :=
    @g_anbi1d (.classEq (.cv y) A) (.classMem (.cv y) (.cv x)) (.classMem A (.cv x)) (.classMem (.cv x) B) p0004
  have p0006 :=
    @g_exbidv (.classEq (.cv y) A) (syn_wa (.classMem (.cv y) (.cv x)) (.classMem (.cv x) B)) (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) B)) x (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_uni y x B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0008_e01_recanon : Nominal.NPrf (.classEq (syn_cuni B) (.cab y (syn_wex x (syn_wa (.classMem (.cv y) (.cv x)) (.classMem (.cv x) B))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cuni syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        ·
          exact Nominal.RecanonTransportDev.TRecanonClass.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonClass.cab
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0007
  have p0008 :=
    @g_elab2g (syn_wex x (syn_wa (.classMem (.cv y) (.cv x)) (.classMem (.cv x) B))) (syn_wex x (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) B))) y A (syn_cuni B) (syn_cvv) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0006 p0008_e01_recanon
  have p0009 :=
    @g_pm5_21nii (.classMem A (syn_cuni B)) (.classMem A (syn_cvv)) (syn_wex x (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) B))) p0000 p0003 p0008
  exact p0009

noncomputable def g_eluni2
    (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cuni B)) (syn_wrex x B (.classMem A (.cv x)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_exancom (.classMem A (.cv x)) (.classMem (.cv x) B) x
  have p0001 :=
    @g_eluni x A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0002 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex x B (.classMem A (.cv x)))))
  have p0003 :=
    @g_n_3bitr4i (syn_wex x (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) B))) (syn_wex x (syn_wa (.classMem (.cv x) B) (.classMem A (.cv x)))) (.classMem A (syn_cuni B)) (syn_wrex x B (.classMem A (.cv x))) p0000 p0001 p0002
  exact p0003

noncomputable def g_elunii
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A B) (.classMem B C)) (.classMem A (syn_cuni C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_eleq2 (.cv x) B A
  have p0001 :=
    @g_eleq1 (.cv x) B C
  have p0002 :=
    @g_anbi12d (.classEq (.cv x) B) (.classMem A (.cv x)) (.classMem A B) (.classMem (.cv x) C) (.classMem B C) p0000 p0001
  have p0003 :=
    @g_spcegv (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) C)) (syn_wa (.classMem A B) (.classMem B C)) x B C (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0002
  have p0004 :=
    @g_anabsi7 (.classMem A B) (.classMem B C) (syn_wex x (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) C))) p0003
  have p0005 :=
    @g_eluni x A C (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0006 :=
    @g_sylibr (syn_wa (.classMem A B) (.classMem B C)) (syn_wex x (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) C))) (.classMem A (syn_cuni C)) p0004 p0005
  exact p0006

noncomputable def g_nfuni
    (x : Var) (A : Class) (hyp_nfuni_1 : Nominal.NPrf (syn_wnfc x A)) :
    Nominal.NPrf (syn_wnfc x (syn_cuni A)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have p0000 :=
    @g_dfuni2 y z A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_nfv (.classMem (.cv y) (.cv z)) x (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0002 :=
    @g_nfrex (.classMem (.cv y) (.cv z)) x z A hyp_nfuni_1 p0001
  have p0003 :=
    @g_nfab (syn_wrex z A (.classMem (.cv y) (.cv z))) x y p0002
  have p0004 :=
    @g_nfcxfr x (syn_cuni A) (.cab y (syn_wrex z A (.classMem (.cv y) (.cv z)))) p0000 p0003
  exact p0004

noncomputable def g_unieq
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cuni A) (syn_cuni B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have p0000 :=
    @g_rexeq (.classMem (.cv y) (.cv x)) x A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_abbidv (.classEq A B) (syn_wrex x A (.classMem (.cv y) (.cv x))) (syn_wrex x B (.classMem (.cv y) (.cv x))) y (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0000
  have p0002 :=
    @g_dfuni2 y x A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_dfuni2 y x B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (.cab y (syn_wrex x A (.classMem (.cv y) (.cv x)))) (.cab y (syn_wrex x B (.classMem (.cv y) (.cv x)))) (syn_cuni A) (syn_cuni B) p0001 p0002 p0003
  exact p0004

noncomputable def g_unieqi
    (A : Class) (B : Class) (hyp_unieqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cuni A) (syn_cuni B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_unieq A B
  have p0001 :=
    Nominal.mp hyp_unieqi_1 p0000
  exact p0001

noncomputable def g_unieqd
    (ph : Wff) (A : Class) (B : Class) (hyp_unieqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cuni A) (syn_cuni B))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_unieq A B
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cuni A) (syn_cuni B)) hyp_unieqd_1 p0000
  exact p0001

noncomputable def g_eluniab
    (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cuni (.cab x ph))) (syn_wex x (syn_wa (.classMem A (.cv x)) ph))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_eluni y A (.cab x ph) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_nfv (.classMem A (.cv y)) x (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0002 :=
    @g_nfsab1 ph x y (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_nfan (.classMem A (.cv y)) (.classMem (.cv y) (.cab x ph)) x p0001 p0002
  have p0004 :=
    @g_nfv (syn_wa (.classMem A (.cv x)) ph) y (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0005 :=
    @g_eleq2 (.cv y) (.cv x) A
  have p0006 :=
    @g_eleq1 (.cv y) (.cv x) (.cab x ph)
  have p0007 :=
    @g_abid ph x
  have p0008 :=
    @g_syl6bb (.classEq (.cv y) (.cv x)) (.classMem (.cv y) (.cab x ph)) (.classMem (.cv x) (.cab x ph)) ph p0006 p0007
  have p0009 :=
    @g_anbi12d (.classEq (.cv y) (.cv x)) (.classMem A (.cv y)) (.classMem A (.cv x)) (.classMem (.cv y) (.cab x ph)) ph p0005 p0008
  have p0010_e02_recanon : Nominal.NPrf (.imp (.objEq y x) (syn_wb (syn_wa (.classMem A (.cv y)) (.classMem (.cv y) (.cab x ph))) (syn_wa (.classMem A (.cv x)) ph))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0009
  have p0010 :=
    @g_cbvex (syn_wa (.classMem A (.cv y)) (.classMem (.cv y) (.cab x ph))) (syn_wa (.classMem A (.cv x)) ph) y x p0003 p0004 p0010_e02_recanon
  have p0011 :=
    @g_bitri (.classMem A (syn_cuni (.cab x ph))) (syn_wex y (syn_wa (.classMem A (.cv y)) (.classMem (.cv y) (.cab x ph)))) (syn_wex x (syn_wa (.classMem A (.cv x)) ph)) p0000 p0010
  exact p0011

noncomputable def g_unipr
    (A : Class) (B : Class) (hyp_unipr_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_unipr_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cuni (syn_cpr A B)) (syn_cun A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_vex y
  have p0001 :=
    @g_elpr (.cv y) A B p0000
  have p0002 :=
    @g_anbi2i (.classMem (.cv y) (syn_cpr A B)) (syn_wo (.classEq (.cv y) A) (.classEq (.cv y) B)) (.objMem x y) p0001
  have p0003 :=
    @g_andi (.objMem x y) (.classEq (.cv y) A) (.classEq (.cv y) B)
  have p0004 :=
    @g_bitri (syn_wa (.objMem x y) (.classMem (.cv y) (syn_cpr A B))) (syn_wa (.objMem x y) (syn_wo (.classEq (.cv y) A) (.classEq (.cv y) B))) (syn_wo (syn_wa (.objMem x y) (.classEq (.cv y) A)) (syn_wa (.objMem x y) (.classEq (.cv y) B))) p0002 p0003
  have p0005 :=
    @g_exbii (syn_wa (.objMem x y) (.classMem (.cv y) (syn_cpr A B))) (syn_wo (syn_wa (.objMem x y) (.classEq (.cv y) A)) (syn_wa (.objMem x y) (.classEq (.cv y) B))) y p0004
  have p0006 :=
    @g_n_19_43 (syn_wa (.objMem x y) (.classEq (.cv y) A)) (syn_wa (.objMem x y) (.classEq (.cv y) B)) y
  have p0007 :=
    @g_bitri (syn_wex y (syn_wa (.objMem x y) (.classMem (.cv y) (syn_cpr A B)))) (syn_wex y (syn_wo (syn_wa (.objMem x y) (.classEq (.cv y) A)) (syn_wa (.objMem x y) (.classEq (.cv y) B)))) (syn_wo (syn_wex y (syn_wa (.objMem x y) (.classEq (.cv y) A))) (syn_wex y (syn_wa (.objMem x y) (.classEq (.cv y) B)))) p0005 p0006
  have p0008 :=
    @g_eluni y (.cv x) (syn_cpr A B) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0009 :=
    @g_elun (.cv x) A B
  have p0010 :=
    @g_clel3 y (.cv x) A (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) hyp_unipr_1
  have p0011 :=
    @g_exancom (.classEq (.cv y) A) (.objMem x y) y
  have p0012_e00_recanon : Nominal.NPrf (syn_wb (.classMem (.cv x) A) (syn_wex y (syn_wa (.classEq (.cv y) A) (.objMem x y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0010
  have p0012 :=
    @g_bitri (.classMem (.cv x) A) (syn_wex y (syn_wa (.classEq (.cv y) A) (.objMem x y))) (syn_wex y (syn_wa (.objMem x y) (.classEq (.cv y) A))) p0012_e00_recanon p0011
  have p0013 :=
    @g_clel3 y (.cv x) B (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) hyp_unipr_2
  have p0014 :=
    @g_exancom (.classEq (.cv y) B) (.objMem x y) y
  have p0015_e00_recanon : Nominal.NPrf (syn_wb (.classMem (.cv x) B) (syn_wex y (syn_wa (.classEq (.cv y) B) (.objMem x y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0013
  have p0015 :=
    @g_bitri (.classMem (.cv x) B) (syn_wex y (syn_wa (.classEq (.cv y) B) (.objMem x y))) (syn_wex y (syn_wa (.objMem x y) (.classEq (.cv y) B))) p0015_e00_recanon p0014
  have p0016 :=
    @g_orbi12i (.classMem (.cv x) A) (syn_wex y (syn_wa (.objMem x y) (.classEq (.cv y) A))) (.classMem (.cv x) B) (syn_wex y (syn_wa (.objMem x y) (.classEq (.cv y) B))) p0012 p0015
  have p0017 :=
    @g_bitri (.classMem (.cv x) (syn_cun A B)) (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B)) (syn_wo (syn_wex y (syn_wa (.objMem x y) (.classEq (.cv y) A))) (syn_wex y (syn_wa (.objMem x y) (.classEq (.cv y) B)))) p0009 p0016
  have p0018_e01_recanon : Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_cuni (syn_cpr A B))) (syn_wex y (syn_wa (.objMem x y) (.classMem (.cv y) (syn_cpr A B))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cuni syn_wex syn_wa syn_cpr syn_cun syn_cnin syn_wnan syn_ccompl syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0008
  have p0018 :=
    @g_n_3bitr4i (syn_wex y (syn_wa (.objMem x y) (.classMem (.cv y) (syn_cpr A B)))) (syn_wo (syn_wex y (syn_wa (.objMem x y) (.classEq (.cv y) A))) (syn_wex y (syn_wa (.objMem x y) (.classEq (.cv y) B)))) (.classMem (.cv x) (syn_cuni (syn_cpr A B))) (.classMem (.cv x) (syn_cun A B)) p0007 p0018_e01_recanon p0017
  have p0019 :=
    @g_eqriv x (syn_cuni (syn_cpr A B)) (syn_cun A B) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0018
  exact p0019

noncomputable def g_unisn
    (A : Class) (hyp_unisn_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cuni (syn_csn A)) A) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_dfsn2 A
  have p0001 :=
    @g_unieqi (syn_csn A) (syn_cpr A A) p0000
  have p0002 :=
    @g_unipr A A hyp_unisn_1 hyp_unisn_1
  have p0003 :=
    @g_unidm A
  have p0004 :=
    @g_n_3eqtri (syn_cuni (syn_csn A)) (syn_cuni (syn_cpr A A)) (syn_cun A A) A p0001 p0002 p0003
  exact p0004

noncomputable def g_unisng
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classEq (syn_cuni (syn_csn A)) A)) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_sneq (.cv x) A
  have p0001 :=
    @g_unieqd (.classEq (.cv x) A) (syn_csn (.cv x)) (syn_csn A) p0000
  have p0002 :=
    @g_id (.classEq (.cv x) A)
  have p0003 :=
    @g_eqeq12d (.classEq (.cv x) A) (syn_cuni (syn_csn (.cv x))) (syn_cuni (syn_csn A)) (.cv x) A p0001 p0002
  have p0004 :=
    @g_vex x
  have p0005 :=
    @g_unisn (.cv x) p0004
  have p0006 :=
    @g_vtoclg (.classEq (syn_cuni (syn_csn (.cv x))) (.cv x)) (.classEq (syn_cuni (syn_csn A)) A) x A V (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0003 p0005
  exact p0006

noncomputable def g_uniun
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cuni (syn_cun A B)) (syn_cun (syn_cuni A) (syn_cuni B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_n_19_43 (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A)) (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) B)) y
  have p0001 :=
    @g_elun (.cv y) A B
  have p0002 :=
    @g_anbi2i (.classMem (.cv y) (syn_cun A B)) (syn_wo (.classMem (.cv y) A) (.classMem (.cv y) B)) (.classMem (.cv x) (.cv y)) p0001
  have p0003 :=
    @g_andi (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A) (.classMem (.cv y) B)
  have p0004 :=
    @g_bitri (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) (syn_cun A B))) (syn_wa (.classMem (.cv x) (.cv y)) (syn_wo (.classMem (.cv y) A) (.classMem (.cv y) B))) (syn_wo (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A)) (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) B))) p0002 p0003
  have p0005 :=
    @g_exbii (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) (syn_cun A B))) (syn_wo (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A)) (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) B))) y p0004
  have p0006 :=
    @g_eluni y (.cv x) A (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0007 :=
    @g_eluni y (.cv x) B (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0008 :=
    @g_orbi12i (.classMem (.cv x) (syn_cuni A)) (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A))) (.classMem (.cv x) (syn_cuni B)) (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) B))) p0006 p0007
  have p0009 :=
    @g_n_3bitr4i (syn_wex y (syn_wo (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A)) (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) B)))) (syn_wo (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A))) (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) B)))) (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) (syn_cun A B)))) (syn_wo (.classMem (.cv x) (syn_cuni A)) (.classMem (.cv x) (syn_cuni B))) p0000 p0005 p0008
  have p0010 :=
    @g_eluni y (.cv x) (syn_cun A B) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0011 :=
    @g_elun (.cv x) (syn_cuni A) (syn_cuni B)
  have p0012 :=
    @g_n_3bitr4i (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) (syn_cun A B)))) (syn_wo (.classMem (.cv x) (syn_cuni A)) (.classMem (.cv x) (syn_cuni B))) (.classMem (.cv x) (syn_cuni (syn_cun A B))) (.classMem (.cv x) (syn_cun (syn_cuni A) (syn_cuni B))) p0009 p0010 p0011
  have p0013 :=
    @g_eqriv x (syn_cuni (syn_cun A B)) (syn_cun (syn_cuni A) (syn_cuni B)) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0012
  exact p0013

noncomputable def g_uniss
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wss (syn_cuni A) (syn_cuni B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_ssel A B (.cv y)
  have p0001 :=
    @g_anim2d (syn_wss A B) (.classMem (.cv y) A) (.classMem (.cv y) B) (.classMem (.cv x) (.cv y)) p0000
  have p0002 :=
    @g_eximdv (syn_wss A B) (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A)) (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) B)) y (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0001
  have p0003 :=
    @g_eluni y (.cv x) A (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0004 :=
    @g_eluni y (.cv x) B (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0005 :=
    @g_n_3imtr4g (syn_wss A B) (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A))) (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) B))) (.classMem (.cv x) (syn_cuni A)) (.classMem (.cv x) (syn_cuni B)) p0002 p0003 p0004
  have p0006 :=
    @g_ssrdv (syn_wss A B) x (syn_cuni A) (syn_cuni B) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0005
  exact p0006

noncomputable def g_ssuni
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wss A B) (.classMem B C)) (syn_wss A (syn_cuni C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have p0000 :=
    @g_eleq2 (.cv x) B (.cv y)
  have p0001 :=
    @g_imbi1d (.classEq (.cv x) B) (.classMem (.cv y) (.cv x)) (.classMem (.cv y) B) (.classMem (.cv y) (syn_cuni C)) p0000
  have p0002 :=
    @g_elunii (.cv y) (.cv x) C
  have p0003 :=
    @g_expcom (.classMem (.cv y) (.cv x)) (.classMem (.cv x) C) (.classMem (.cv y) (syn_cuni C)) p0002
  have p0004 :=
    @g_vtoclga (.imp (.classMem (.cv y) (.cv x)) (.classMem (.cv y) (syn_cuni C))) (.imp (.classMem (.cv y) B) (.classMem (.cv y) (syn_cuni C))) x B C (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0001 p0003
  have p0005 :=
    @g_imim2d (.classMem B C) (.classMem (.cv y) B) (.classMem (.cv y) (syn_cuni C)) (.classMem (.cv y) A) p0004
  have p0006 :=
    @g_alimdv (.classMem B C) (.imp (.classMem (.cv y) A) (.classMem (.cv y) B)) (.imp (.classMem (.cv y) A) (.classMem (.cv y) (syn_cuni C))) y (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0005
  have p0007 :=
    @g_dfss2 y A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0008 :=
    @g_dfss2 y A (syn_cuni C) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0009 :=
    @g_n_3imtr4g (.classMem B C) (.all y (.imp (.classMem (.cv y) A) (.classMem (.cv y) B))) (.all y (.imp (.classMem (.cv y) A) (.classMem (.cv y) (syn_cuni C)))) (syn_wss A B) (syn_wss A (syn_cuni C)) p0006 p0007 p0008
  have p0010 :=
    @g_impcom (.classMem B C) (syn_wss A B) (syn_wss A (syn_cuni C)) p0009
  exact p0010

noncomputable def g_uni0b
    (A : Class) :
    Nominal.NPrf (syn_wb (.classEq (syn_cuni A) (syn_c0)) (syn_wss A (syn_csn (syn_c0)))) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_elsn x (syn_c0) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_ralbii (.classMem (.cv x) (syn_csn (syn_c0))) (.classEq (.cv x) (syn_c0)) x A p0000
  have p0002 :=
    @g_dfss3 x A (syn_csn (syn_c0)) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_neq0 y (syn_cuni A) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0004 :=
    @g_rexcom4 (.classMem (.cv y) (.cv x)) x y A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0005 :=
    @g_neq0 y (.cv x) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0006 :=
    @g_rexbii (.neg (.classEq (.cv x) (syn_c0))) (syn_wex y (.classMem (.cv y) (.cv x))) x A p0005
  have p0007 :=
    @g_eluni2 x (.cv y) A (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0008 :=
    @g_exbii (.classMem (.cv y) (syn_cuni A)) (syn_wrex x A (.classMem (.cv y) (.cv x))) y p0007
  have p0009 :=
    @g_n_3bitr4ri (syn_wrex x A (syn_wex y (.classMem (.cv y) (.cv x)))) (syn_wex y (syn_wrex x A (.classMem (.cv y) (.cv x)))) (syn_wrex x A (.neg (.classEq (.cv x) (syn_c0)))) (syn_wex y (.classMem (.cv y) (syn_cuni A))) p0004 p0006 p0008
  have p0010 :=
    @g_rexnal (.classEq (.cv x) (syn_c0)) x A
  have p0011 :=
    @g_n_3bitri (.neg (.classEq (syn_cuni A) (syn_c0))) (syn_wex y (.classMem (.cv y) (syn_cuni A))) (syn_wrex x A (.neg (.classEq (.cv x) (syn_c0)))) (.neg (syn_wral x A (.classEq (.cv x) (syn_c0)))) p0003 p0009 p0010
  have p0012 :=
    @g_con4bii (.classEq (syn_cuni A) (syn_c0)) (syn_wral x A (.classEq (.cv x) (syn_c0))) p0011
  have p0013 :=
    @g_n_3bitr4ri (syn_wral x A (.classMem (.cv x) (syn_csn (syn_c0)))) (syn_wral x A (.classEq (.cv x) (syn_c0))) (syn_wss A (syn_csn (syn_c0))) (.classEq (syn_cuni A) (syn_c0)) p0001 p0002 p0012
  exact p0013

noncomputable def g_uni0
     :
    Nominal.NPrf (.classEq (syn_cuni (syn_c0)) (syn_c0)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_0ss (syn_csn (syn_c0))
  have p0001 :=
    @g_uni0b (syn_c0)
  have p0002 :=
    @g_mpbir (.classEq (syn_cuni (syn_c0)) (syn_c0)) (syn_wss (syn_c0) (syn_csn (syn_c0))) p0000 p0001
  exact p0002

noncomputable def g_elssuni
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem A B) (syn_wss A (syn_cuni B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_ssid A
  have p0001 :=
    @g_ssuni A A B
  have p0002 :=
    @g_mpan (syn_wss A A) (.classMem A B) (syn_wss A (syn_cuni B)) p0000 p0001
  exact p0002

noncomputable def g_dfint2
    (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_cint A) (.cab x (syn_wral y A (.classMem (.cv x) (.cv y))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_int x y A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral y A (.classMem (.cv x) (.cv y)))))
  have p0002 :=
    @g_abbii (syn_wral y A (.classMem (.cv x) (.cv y))) (.all y (.imp (.classMem (.cv y) A) (.classMem (.cv x) (.cv y)))) x p0001
  have p0003_e00_recanon : Nominal.NPrf (.classEq (syn_cint A) (.cab x (.all y (.imp (.classMem (.cv y) A) (.classMem (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cint
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cint, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        ·
          exact Nominal.RecanonTransportDev.TRecanonClass.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonClass.cab
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
      )
      p0000
  have p0003 :=
    @g_eqtr4i (syn_cint A) (.cab x (.all y (.imp (.classMem (.cv y) A) (.classMem (.cv x) (.cv y))))) (.cab x (syn_wral y A (.classMem (.cv x) (.cv y)))) p0003_e00_recanon p0002
  exact p0003

noncomputable def g_inteq
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cint A) (syn_cint B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_raleq (.classMem (.cv x) (.cv y)) y A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_abbidv (.classEq A B) (syn_wral y A (.classMem (.cv x) (.cv y))) (syn_wral y B (.classMem (.cv x) (.cv y))) x (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0000
  have p0002 :=
    @g_dfint2 x y A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_dfint2 x y B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (.cab x (syn_wral y A (.classMem (.cv x) (.cv y)))) (.cab x (syn_wral y B (.classMem (.cv x) (.cv y)))) (syn_cint A) (syn_cint B) p0001 p0002 p0003
  exact p0004

noncomputable def g_inteqi
    (A : Class) (B : Class) (hyp_inteqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cint A) (syn_cint B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_inteq A B
  have p0001 :=
    Nominal.mp hyp_inteqi_1 p0000
  exact p0001

noncomputable def g_elint
    (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (hyp_elint_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cint B)) (.all x (.imp (.classMem (.cv x) B) (.classMem A (.cv x))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_eleq1 (.cv y) A (.cv x)
  have p0001 :=
    @g_imbi2d (.classEq (.cv y) A) (.classMem (.cv y) (.cv x)) (.classMem A (.cv x)) (.classMem (.cv x) B) p0000
  have p0002 :=
    @g_albidv (.classEq (.cv y) A) (.imp (.classMem (.cv x) B) (.classMem (.cv y) (.cv x))) (.imp (.classMem (.cv x) B) (.classMem A (.cv x))) x (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_int y x B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0004_e02_recanon : Nominal.NPrf (.classEq (syn_cint B) (.cab y (.all x (.imp (.classMem (.cv x) B) (.classMem (.cv y) (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cint
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cint, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        ·
          exact Nominal.RecanonTransportDev.TRecanonClass.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonClass.cab
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
      )
      p0003
  have p0004 :=
    @g_elab2 (.all x (.imp (.classMem (.cv x) B) (.classMem (.cv y) (.cv x)))) (.all x (.imp (.classMem (.cv x) B) (.classMem A (.cv x)))) y A (syn_cint B) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) hyp_elint_1 p0002 p0004_e02_recanon
  exact p0004

noncomputable def g_elint2
    (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (hyp_elint2_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cint B)) (syn_wral x B (.classMem A (.cv x)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_elint x A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) hyp_elint2_1
  have p0001 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral x B (.classMem A (.cv x)))))
  have p0002 :=
    @g_bitr4i (.classMem A (syn_cint B)) (.all x (.imp (.classMem (.cv x) B) (.classMem A (.cv x)))) (syn_wral x B (.classMem A (.cv x))) p0000 p0001
  exact p0002

noncomputable def g_elintab
    (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) (hyp_inteqab_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cint (.cab x ph))) (.all x (.imp ph (.classMem A (.cv x))))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_elint y A (.cab x ph) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) hyp_inteqab_1
  have p0001 :=
    @g_nfsab1 ph x y (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0002 :=
    @g_nfv (.classMem A (.cv y)) x (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_nfim (.classMem (.cv y) (.cab x ph)) (.classMem A (.cv y)) x p0001 p0002
  have p0004 :=
    @g_nfv (.imp ph (.classMem A (.cv x))) y (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0005 :=
    @g_eleq1 (.cv y) (.cv x) (.cab x ph)
  have p0006 :=
    @g_abid ph x
  have p0007 :=
    @g_syl6bb (.classEq (.cv y) (.cv x)) (.classMem (.cv y) (.cab x ph)) (.classMem (.cv x) (.cab x ph)) ph p0005 p0006
  have p0008 :=
    @g_eleq2 (.cv y) (.cv x) A
  have p0009 :=
    @g_imbi12d (.classEq (.cv y) (.cv x)) (.classMem (.cv y) (.cab x ph)) ph (.classMem A (.cv y)) (.classMem A (.cv x)) p0007 p0008
  have p0010_e02_recanon : Nominal.NPrf (.imp (.objEq y x) (syn_wb (.imp (.classMem (.cv y) (.cab x ph)) (.classMem A (.cv y))) (.imp ph (.classMem A (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0009
  have p0010 :=
    @g_cbval (.imp (.classMem (.cv y) (.cab x ph)) (.classMem A (.cv y))) (.imp ph (.classMem A (.cv x))) y x p0003 p0004 p0010_e02_recanon
  have p0011 :=
    @g_bitri (.classMem A (syn_cint (.cab x ph))) (.all y (.imp (.classMem (.cv y) (.cab x ph)) (.classMem A (.cv y)))) (.all x (.imp ph (.classMem A (.cv x)))) p0000 p0010
  exact p0011

noncomputable def g_intss1
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem A B) (syn_wss (syn_cint B) A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_vex x
  have p0001 :=
    @g_elint y (.cv x) B (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0000
  have p0002 :=
    @g_eleq1 (.cv y) A B
  have p0003 :=
    @g_eleq2 (.cv y) A (.cv x)
  have p0004 :=
    @g_imbi12d (.classEq (.cv y) A) (.classMem (.cv y) B) (.classMem A B) (.classMem (.cv x) (.cv y)) (.classMem (.cv x) A) p0002 p0003
  have p0005 :=
    @g_spcgv (.imp (.classMem (.cv y) B) (.classMem (.cv x) (.cv y))) (.imp (.classMem A B) (.classMem (.cv x) A)) y A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0004
  have p0006 :=
    @g_pm2_43a (.all y (.imp (.classMem (.cv y) B) (.classMem (.cv x) (.cv y)))) (.classMem A B) (.classMem (.cv x) A) p0005
  have p0007 :=
    @g_syl5bi (.classMem (.cv x) (syn_cint B)) (.all y (.imp (.classMem (.cv y) B) (.classMem (.cv x) (.cv y)))) (.classMem A B) (.classMem (.cv x) A) p0001 p0006
  have p0008 :=
    @g_ssrdv (.classMem A B) x (syn_cint B) A (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cint, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0007
  exact p0008

noncomputable def g_ssint
    (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (syn_wb (syn_wss A (syn_cint B)) (syn_wral x B (syn_wss A (.cv x)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_dfss3 y A (syn_cint B) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cint, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_vex y
  have p0002 :=
    @g_elint2 x (.cv y) B (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0001
  have p0003 :=
    @g_ralbii (.classMem (.cv y) (syn_cint B)) (syn_wral x B (.classMem (.cv y) (.cv x))) y A p0002
  have p0004 :=
    @g_ralcom (.classMem (.cv y) (.cv x)) y x A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0005 :=
    @g_dfss3 y A (.cv x) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0006 :=
    @g_ralbii (syn_wss A (.cv x)) (syn_wral y A (.classMem (.cv y) (.cv x))) x B p0005
  have p0007 :=
    @g_bitr4i (syn_wral y A (syn_wral x B (.classMem (.cv y) (.cv x)))) (syn_wral x B (syn_wral y A (.classMem (.cv y) (.cv x)))) (syn_wral x B (syn_wss A (.cv x))) p0004 p0006
  have p0008 :=
    @g_n_3bitri (syn_wss A (syn_cint B)) (syn_wral y A (.classMem (.cv y) (syn_cint B))) (syn_wral y A (syn_wral x B (.classMem (.cv y) (.cv x)))) (syn_wral x B (syn_wss A (.cv x))) p0000 p0003 p0007
  exact p0008

noncomputable def g_ssintab
    (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (syn_wss A (syn_cint (.cab x ph))) (.all x (.imp ph (syn_wss A (.cv x))))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_ssint y A (.cab x ph) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_sseq2 (.cv y) (.cv x) A
  have p0002_e00_recanon : Nominal.NPrf (.imp (.objEq y x) (syn_wb (syn_wss A (.cv y)) (syn_wss A (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0001
  have p0002 :=
    @g_ralab2 ph (syn_wss A (.cv y)) (syn_wss A (.cv x)) y x (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0002_e00_recanon
  have p0003 :=
    @g_bitri (syn_wss A (syn_cint (.cab x ph))) (syn_wral y (.cab x ph) (syn_wss A (.cv y))) (.all x (.imp ph (syn_wss A (.cv x)))) p0000 p0002
  exact p0003

noncomputable def g_ssmin
    (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wss A (syn_cint (.cab x (syn_wa (syn_wss A (.cv x)) ph)))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_ssintab (syn_wa (syn_wss A (.cv x)) ph) x A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_simpl (syn_wss A (.cv x)) ph
  have p0002 :=
    @g_mpgbir (syn_wss A (syn_cint (.cab x (syn_wa (syn_wss A (.cv x)) ph)))) (.imp (syn_wa (syn_wss A (.cv x)) ph) (syn_wss A (.cv x))) x p0000 p0001
  exact p0002

noncomputable def g_eliun
    (x : Var) (A : Class) (B : Class) (C : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_ciun x B C)) (syn_wrex x B (.classMem A C))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_elex A (syn_ciun x B C)
  have p0001 :=
    @g_elex A C
  have p0002 :=
    @g_rexlimivw (.classMem A C) (.classMem A (syn_cvv)) x B (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0001
  have p0003 :=
    @g_eleq1 (.cv y) A C
  have p0004 :=
    @g_rexbidv (.classEq (.cv y) A) (.classMem (.cv y) C) (.classMem A C) x B (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iun x y B C (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0006 :=
    @g_elab2g (syn_wrex x B (.classMem (.cv y) C)) (syn_wrex x B (.classMem A C)) y A (syn_ciun x B C) (syn_cvv) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0004 p0005
  have p0007 :=
    @g_pm5_21nii (.classMem A (syn_ciun x B C)) (.classMem A (syn_cvv)) (syn_wrex x B (.classMem A C)) p0000 p0002 p0006
  exact p0007

noncomputable def g_ss2iun
    (x : Var) (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wral x A (syn_wss B C)) (syn_wss (syn_ciun x A B) (syn_ciun x A C))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_ssel B C (.cv y)
  have p0001 :=
    @g_ralimi (syn_wss B C) (.imp (.classMem (.cv y) B) (.classMem (.cv y) C)) x A p0000
  have p0002 :=
    @g_rexim (.classMem (.cv y) B) (.classMem (.cv y) C) x A
  have p0003 :=
    @g_syl (syn_wral x A (syn_wss B C)) (syn_wral x A (.imp (.classMem (.cv y) B) (.classMem (.cv y) C))) (.imp (syn_wrex x A (.classMem (.cv y) B)) (syn_wrex x A (.classMem (.cv y) C))) p0001 p0002
  have p0004 :=
    @g_eliun x (.cv y) A B (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0005 :=
    @g_eliun x (.cv y) A C (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0006 :=
    @g_n_3imtr4g (syn_wral x A (syn_wss B C)) (syn_wrex x A (.classMem (.cv y) B)) (syn_wrex x A (.classMem (.cv y) C)) (.classMem (.cv y) (syn_ciun x A B)) (.classMem (.cv y) (syn_ciun x A C)) p0003 p0004 p0005
  have p0007 :=
    @g_ssrdv (syn_wral x A (syn_wss B C)) y (syn_ciun x A B) (syn_ciun x A C) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0006
  exact p0007

noncomputable def g_iuneq2
    (x : Var) (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wral x A (.classEq B C)) (.classEq (syn_ciun x A B) (syn_ciun x A C))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_ss2iun x A B C
  have p0001 :=
    @g_ss2iun x A C B
  have p0002 :=
    @g_anim12i (syn_wral x A (syn_wss B C)) (syn_wss (syn_ciun x A B) (syn_ciun x A C)) (syn_wral x A (syn_wss C B)) (syn_wss (syn_ciun x A C) (syn_ciun x A B)) p0000 p0001
  have p0003 :=
    @g_eqss B C
  have p0004 :=
    @g_ralbii (.classEq B C) (syn_wa (syn_wss B C) (syn_wss C B)) x A p0003
  have p0005 :=
    @g_r19_26 (syn_wss B C) (syn_wss C B) x A
  have p0006 :=
    @g_bitri (syn_wral x A (.classEq B C)) (syn_wral x A (syn_wa (syn_wss B C) (syn_wss C B))) (syn_wa (syn_wral x A (syn_wss B C)) (syn_wral x A (syn_wss C B))) p0004 p0005
  have p0007 :=
    @g_eqss (syn_ciun x A B) (syn_ciun x A C)
  have p0008 :=
    @g_n_3imtr4i (syn_wa (syn_wral x A (syn_wss B C)) (syn_wral x A (syn_wss C B))) (syn_wa (syn_wss (syn_ciun x A B) (syn_ciun x A C)) (syn_wss (syn_ciun x A C) (syn_ciun x A B))) (syn_wral x A (.classEq B C)) (.classEq (syn_ciun x A B) (syn_ciun x A C)) p0002 p0006 p0007
  exact p0008

noncomputable def g_iuneq2i
    (x : Var) (A : Class) (B : Class) (C : Class) (hyp_iuneq2i_1 : Nominal.NPrf (.imp (.classMem (.cv x) A) (.classEq B C))) :
    Nominal.NPrf (.classEq (syn_ciun x A B) (syn_ciun x A C)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_iuneq2 x A B C
  have p0001 :=
    @g_mprg (.classEq B C) (.classEq (syn_ciun x A B) (syn_ciun x A C)) x A p0000 hyp_iuneq2i_1
  exact p0001

noncomputable def g_nfiun
    (x : Var) (y : Var) (A : Class) (B : Class) (hyp_nfiun_1 : Nominal.NPrf (syn_wnfc y A)) (hyp_nfiun_2 : Nominal.NPrf (syn_wnfc y B)) :
    Nominal.NPrf (syn_wnfc y (syn_ciun x A B)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iun x z A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_nfcri y z B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) hyp_nfiun_2
  have p0002 :=
    @g_nfrex (.classMem (.cv z) B) y x A hyp_nfiun_1 p0001
  have p0003 :=
    @g_nfab (syn_wrex x A (.classMem (.cv z) B)) y z p0002
  have p0004 :=
    @g_nfcxfr y (syn_ciun x A B) (.cab z (syn_wrex x A (.classMem (.cv z) B))) p0000 p0003
  exact p0004

noncomputable def g_nfiu1
    (x : Var) (A : Class) (B : Class) :
    Nominal.NPrf (syn_wnfc x (syn_ciun x A B)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iun x y A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_nfre1 (.classMem (.cv y) B) x A
  have p0002 :=
    @g_nfab (syn_wrex x A (.classMem (.cv y) B)) x y p0001
  have p0003 :=
    @g_nfcxfr x (syn_ciun x A B) (.cab y (syn_wrex x A (.classMem (.cv y) B))) p0000 p0002
  exact p0003

noncomputable def g_dfiun2g
    (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (syn_wral x A (.classMem B C)) (.classEq (syn_ciun x A B) (syn_cuni (.cab y (syn_wrex x A (.classEq (.cv y) B)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_nfra1 (.classMem B C) x A
  have p0001 :=
    @g_rsp (.classMem B C) x A
  have p0002 :=
    @g_clel3g y (.cv z) B C (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_syl6 (syn_wral x A (.classMem B C)) (.classMem (.cv x) A) (.classMem B C) (syn_wb (.classMem (.cv z) B) (syn_wex y (syn_wa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y))))) p0001 p0002
  have p0004 :=
    @g_imp (syn_wral x A (.classMem B C)) (.classMem (.cv x) A) (syn_wb (.classMem (.cv z) B) (syn_wex y (syn_wa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y))))) p0003
  have p0005 :=
    @g_rexbida (syn_wral x A (.classMem B C)) (.classMem (.cv z) B) (syn_wex y (syn_wa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y)))) x A p0000 p0004
  have p0006 :=
    @g_rexcom4 (syn_wa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y))) x y A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0007 :=
    @g_syl6bb (syn_wral x A (.classMem B C)) (syn_wrex x A (.classMem (.cv z) B)) (syn_wrex x A (syn_wex y (syn_wa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y))))) (syn_wex y (syn_wrex x A (syn_wa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y))))) p0005 p0006
  have p0008 :=
    @g_r19_41v (.classEq (.cv y) B) (.classMem (.cv z) (.cv y)) x A (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0009 :=
    @g_exbii (syn_wrex x A (syn_wa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y)))) (syn_wa (syn_wrex x A (.classEq (.cv y) B)) (.classMem (.cv z) (.cv y))) y p0008
  have p0010 :=
    @g_exancom (syn_wrex x A (.classEq (.cv y) B)) (.classMem (.cv z) (.cv y)) y
  have p0011 :=
    @g_bitri (syn_wex y (syn_wrex x A (syn_wa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y))))) (syn_wex y (syn_wa (syn_wrex x A (.classEq (.cv y) B)) (.classMem (.cv z) (.cv y)))) (syn_wex y (syn_wa (.classMem (.cv z) (.cv y)) (syn_wrex x A (.classEq (.cv y) B)))) p0009 p0010
  have p0012 :=
    @g_syl6bb (syn_wral x A (.classMem B C)) (syn_wrex x A (.classMem (.cv z) B)) (syn_wex y (syn_wrex x A (syn_wa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y))))) (syn_wex y (syn_wa (.classMem (.cv z) (.cv y)) (syn_wrex x A (.classEq (.cv y) B)))) p0007 p0011
  have p0013 :=
    @g_eliun x (.cv z) A B (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0014 :=
    @g_eluniab (syn_wrex x A (.classEq (.cv y) B)) y (.cv z) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0015 :=
    @g_n_3bitr4g (syn_wral x A (.classMem B C)) (syn_wrex x A (.classMem (.cv z) B)) (syn_wex y (syn_wa (.classMem (.cv z) (.cv y)) (syn_wrex x A (.classEq (.cv y) B)))) (.classMem (.cv z) (syn_ciun x A B)) (.classMem (.cv z) (syn_cuni (.cab y (syn_wrex x A (.classEq (.cv y) B))))) p0012 p0013 p0014
  have p0016 :=
    @g_eqrdv (syn_wral x A (.classMem B C)) z (syn_ciun x A B) (syn_cuni (.cab y (syn_wrex x A (.classEq (.cv y) B)))) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0015
  exact p0016

noncomputable def g_dfiun2
    (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) (hyp_dfiun2_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_ciun x A B) (syn_cuni (.cab y (syn_wrex x A (.classEq (.cv y) B))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_dfiun2g x y A B (syn_cvv) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_a1i (.classMem B (syn_cvv)) (.classMem (.cv x) A) hyp_dfiun2_1
  have p0002 :=
    @g_mprg (.classMem B (syn_cvv)) (.classEq (syn_ciun x A B) (syn_cuni (.cab y (syn_wrex x A (.classEq (.cv y) B))))) x A p0000 p0001
  exact p0002

noncomputable def g_cbviun
    (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (hyp_cbviun_1 : Nominal.NPrf (syn_wnfc y B)) (hyp_cbviun_2 : Nominal.NPrf (syn_wnfc x C)) (hyp_cbviun_3 : Nominal.NPrf (.imp (.objEq x y) (.classEq B C))) :
    Nominal.NPrf (.classEq (syn_ciun x A B) (syn_ciun y A C)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_nfcri y z B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) hyp_cbviun_1
  have p0001 :=
    @g_nfcri x z C (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) hyp_cbviun_2
  have p0002_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (.classEq B C)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      hyp_cbviun_3
  have p0002 :=
    @g_eleq2d (.classEq (.cv x) (.cv y)) B C (.cv z) p0002_e00_recanon
  have p0003_e02_recanon : Nominal.NPrf (.imp (.objEq x y) (syn_wb (.classMem (.cv z) B) (.classMem (.cv z) C))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0002
  have p0003 :=
    @g_cbvrex (.classMem (.cv z) B) (.classMem (.cv z) C) x y A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0000 p0001 p0003_e02_recanon
  have p0004 :=
    @g_abbii (syn_wrex x A (.classMem (.cv z) B)) (syn_wrex y A (.classMem (.cv z) C)) z p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iun x z A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iun y z A C (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0007 :=
    @g_n_3eqtr4i (.cab z (syn_wrex x A (.classMem (.cv z) B))) (.cab z (syn_wrex y A (.classMem (.cv z) C))) (syn_ciun x A B) (syn_ciun y A C) p0004 p0005 p0006
  exact p0007

noncomputable def g_iunss
    (x : Var) (A : Class) (B : Class) (C : Class) (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf (syn_wb (syn_wss (syn_ciun x A B) C) (syn_wral x A (syn_wss B C))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iun x y A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_sseq1i (syn_ciun x A B) (.cab y (syn_wrex x A (.classMem (.cv y) B))) C p0000
  have p0002 :=
    @g_abss (syn_wrex x A (.classMem (.cv y) B)) y C (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_dfss2 y B C (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0004 :=
    @g_ralbii (syn_wss B C) (.all y (.imp (.classMem (.cv y) B) (.classMem (.cv y) C))) x A p0003
  have p0005 :=
    @g_ralcom4 (.imp (.classMem (.cv y) B) (.classMem (.cv y) C)) x y A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0006 :=
    @g_r19_23v (.classMem (.cv y) B) (.classMem (.cv y) C) x A (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0007 :=
    @g_albii (syn_wral x A (.imp (.classMem (.cv y) B) (.classMem (.cv y) C))) (.imp (syn_wrex x A (.classMem (.cv y) B)) (.classMem (.cv y) C)) y p0006
  have p0008 :=
    @g_n_3bitrri (syn_wral x A (syn_wss B C)) (syn_wral x A (.all y (.imp (.classMem (.cv y) B) (.classMem (.cv y) C)))) (.all y (syn_wral x A (.imp (.classMem (.cv y) B) (.classMem (.cv y) C)))) (.all y (.imp (syn_wrex x A (.classMem (.cv y) B)) (.classMem (.cv y) C))) p0004 p0005 p0007
  have p0009 :=
    @g_n_3bitri (syn_wss (syn_ciun x A B) C) (syn_wss (.cab y (syn_wrex x A (.classMem (.cv y) B))) C) (.all y (.imp (syn_wrex x A (.classMem (.cv y) B)) (.classMem (.cv y) C))) (syn_wral x A (syn_wss B C)) p0001 p0002 p0008
  exact p0009

noncomputable def g_iunab
    (ph : Wff) (x : Var) (y : Var) (A : Class) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_ciun x A (.cab y ph)) (.cab y (syn_wrex x A ph))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfcv y A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_nfab1 ph y
  have p0002 :=
    @g_nfiun x y A (.cab y ph) p0000 p0001
  have p0003 :=
    @g_nfab1 (syn_wrex x A ph) y
  have p0004 :=
    @g_cleqf y (syn_ciun x A (.cab y ph)) (.cab y (syn_wrex x A ph)) p0002 p0003
  have p0005 :=
    @g_abid ph y
  have p0006 :=
    @g_rexbii (.classMem (.cv y) (.cab y ph)) ph x A p0005
  have p0007 :=
    @g_eliun x (.cv y) A (.cab y ph) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0008 :=
    @g_abid (syn_wrex x A ph) y
  have p0009 :=
    @g_n_3bitr4i (syn_wrex x A (.classMem (.cv y) (.cab y ph))) (syn_wrex x A ph) (.classMem (.cv y) (syn_ciun x A (.cab y ph))) (.classMem (.cv y) (.cab y (syn_wrex x A ph))) p0006 p0007 p0008
  have p0010 :=
    @g_mpgbir (.classEq (syn_ciun x A (.cab y ph)) (.cab y (syn_wrex x A ph))) (syn_wb (.classMem (.cv y) (syn_ciun x A (.cab y ph))) (.classMem (.cv y) (.cab y (syn_wrex x A ph)))) y p0004 p0009
  exact p0010

noncomputable def g_iunid
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (syn_ciun x A (syn_csn (.cv x))) A) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn y (.cv x) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_equcom y x
  have p0002_e00_recanon : Nominal.NPrf (syn_wb (.classEq (.cv y) (.cv x)) (.classEq (.cv x) (.cv y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
      )
      p0001
  have p0002 :=
    @g_abbii (.classEq (.cv y) (.cv x)) (.classEq (.cv x) (.cv y)) y p0002_e00_recanon
  have p0003 :=
    @g_eqtri (syn_csn (.cv x)) (.cab y (.classEq (.cv y) (.cv x))) (.cab y (.classEq (.cv x) (.cv y))) p0000 p0002
  have p0004 :=
    @g_a1i (.classEq (syn_csn (.cv x)) (.cab y (.classEq (.cv x) (.cv y)))) (.classMem (.cv x) A) p0003
  have p0005 :=
    @g_iuneq2i x A (syn_csn (.cv x)) (.cab y (.classEq (.cv x) (.cv y))) p0004
  have p0006 :=
    @g_iunab (.classEq (.cv x) (.cv y)) x y A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0007 :=
    @g_risset x (.cv y) A (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0008 :=
    @g_abbii (.classMem (.cv y) A) (syn_wrex x A (.classEq (.cv x) (.cv y))) y p0007
  have p0009 :=
    @g_abid2 y A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0010 :=
    @g_n_3eqtr2i (syn_ciun x A (.cab y (.classEq (.cv x) (.cv y)))) (.cab y (syn_wrex x A (.classEq (.cv x) (.cv y)))) (.cab y (.classMem (.cv y) A)) A p0006 p0008 p0009
  have p0011 :=
    @g_eqtri (syn_ciun x A (syn_csn (.cv x))) (syn_ciun x A (.cab y (.classEq (.cv x) (.cv y)))) A p0005 p0010
  exact p0011

noncomputable def g_opkeq1
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_copk A C) (syn_copk B C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_sneq A B
  have p0001 :=
    @g_preq1 A B C
  have p0002 :=
    @g_preq12d (.classEq A B) (syn_csn A) (syn_csn B) (syn_cpr A C) (syn_cpr B C) p0000 p0001
  have p0003 :=
    (by simpa [syn_copk] using (Nominal.classEqRefl (syn_copk A C)))
  have p0004 :=
    (by simpa [syn_copk] using (Nominal.classEqRefl (syn_copk B C)))
  have p0005 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cpr (syn_csn A) (syn_cpr A C)) (syn_cpr (syn_csn B) (syn_cpr B C)) (syn_copk A C) (syn_copk B C) p0002 p0003 p0004
  exact p0005

noncomputable def g_opkeq2
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_copk C A) (syn_copk C B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_preq2 A B C
  have p0001 :=
    @g_preq2d (.classEq A B) (syn_cpr C A) (syn_cpr C B) (syn_csn C) p0000
  have p0002 :=
    (by simpa [syn_copk] using (Nominal.classEqRefl (syn_copk C A)))
  have p0003 :=
    (by simpa [syn_copk] using (Nominal.classEqRefl (syn_copk C B)))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cpr (syn_csn C) (syn_cpr C A)) (syn_cpr (syn_csn C) (syn_cpr C B)) (syn_copk C A) (syn_copk C B) p0001 p0002 p0003
  exact p0004

noncomputable def g_opkeq12
    (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf (.imp (syn_wa (.classEq A C) (.classEq B D)) (.classEq (syn_copk A B) (syn_copk C D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_opkeq1 A C B
  have p0001 :=
    @g_opkeq2 B D C
  have p0002 :=
    @g_sylan9eq (.classEq A C) (.classEq B D) (syn_copk A B) (syn_copk C B) (syn_copk C D) p0000 p0001
  exact p0002

noncomputable def g_opkeq2i
    (A : Class) (B : Class) (C : Class) (hyp_opkeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_copk C A) (syn_copk C B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_opkeq2 A B C
  have p0001 :=
    Nominal.mp hyp_opkeq1i_1 p0000
  exact p0001

noncomputable def g_opkeq1d
    (ph : Wff) (A : Class) (B : Class) (C : Class) (hyp_opkeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_copk A C) (syn_copk B C))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_opkeq1 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_copk A C) (syn_copk B C)) hyp_opkeq1d_1 p0000
  exact p0001

noncomputable def g_opkeq2d
    (ph : Wff) (A : Class) (B : Class) (C : Class) (hyp_opkeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_copk C A) (syn_copk C B))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_opkeq2 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_copk C A) (syn_copk C B)) hyp_opkeq1d_1 p0000
  exact p0001

noncomputable def g_opkeq12d
    (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class) (hyp_opkeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) (hyp_opkeq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq (syn_copk A C) (syn_copk B D))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_opkeq12 A C B D
  have p0001 :=
    @g_syl2anc ph (.classEq A B) (.classEq C D) (.classEq (syn_copk A C) (syn_copk B D)) hyp_opkeq1d_1 hyp_opkeq12d_2 p0000
  exact p0001

noncomputable def g_compldif
    (A : Class) :
    Nominal.NPrf (.classEq (syn_ccompl A) (syn_cdif (syn_cvv) A)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_cdif] using (Nominal.classEqRefl (syn_cdif (syn_cvv) A)))
  have p0001 :=
    @g_incom (syn_cvv) (syn_ccompl A)
  have p0002 :=
    @g_inv1 (syn_ccompl A)
  have p0003 :=
    @g_n_3eqtrri (syn_cdif (syn_cvv) A) (syn_cin (syn_cvv) (syn_ccompl A)) (syn_cin (syn_ccompl A) (syn_cvv)) (syn_ccompl A) p0000 p0001 p0002
  exact p0003

noncomputable def g_complV
     :
    Nominal.NPrf (.classEq (syn_ccompl (syn_cvv)) (syn_c0)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_compldif (syn_cvv)
  have p0001 :=
    (by simpa [syn_c0] using (Nominal.classEqRefl (syn_c0)))
  have p0002 :=
    @g_eqtr4i (syn_ccompl (syn_cvv)) (syn_cdif (syn_cvv) (syn_cvv)) (syn_c0) p0000 p0001
  exact p0002

noncomputable def g_nincompl
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cnin A (syn_ccompl A)) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have p0000 :=
    @g_eqv x (syn_cnin A (syn_ccompl A)) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_pm3_24 (.classMem (.cv x) A)
  have p0002 :=
    @g_vex x
  have p0003 :=
    @g_elnin (.cv x) A (syn_ccompl A) p0002
  have p0004 :=
    @g_elcompl (.cv x) A p0002
  have p0005 :=
    @g_nanbi2i (.classMem (.cv x) (syn_ccompl A)) (.neg (.classMem (.cv x) A)) (.classMem (.cv x) A) p0004
  have p0006 :=
    (by simpa [syn_wb, syn_wnan] using (Nominal.biimpRefl (syn_wnan (.classMem (.cv x) A) (.neg (.classMem (.cv x) A)))))
  have p0007 :=
    @g_n_3bitri (.classMem (.cv x) (syn_cnin A (syn_ccompl A))) (syn_wnan (.classMem (.cv x) A) (.classMem (.cv x) (syn_ccompl A))) (syn_wnan (.classMem (.cv x) A) (.neg (.classMem (.cv x) A))) (.neg (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) A)))) p0003 p0005 p0006
  have p0008 :=
    @g_mpbir (.classMem (.cv x) (syn_cnin A (syn_ccompl A))) (.neg (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) A)))) p0001 p0007
  have p0009 :=
    @g_mpgbir (.classEq (syn_cnin A (syn_ccompl A)) (syn_cvv)) (.classMem (.cv x) (syn_cnin A (syn_ccompl A))) x p0000 p0008
  exact p0009

noncomputable def g_incompl
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cin A (syn_ccompl A)) (syn_c0)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_cin] using (Nominal.classEqRefl (syn_cin A (syn_ccompl A))))
  have p0001 :=
    @g_nincompl A
  have p0002 :=
    @g_compleqi (syn_cnin A (syn_ccompl A)) (syn_cvv) p0001
  have p0003 :=
    @g_complV
  have p0004 :=
    @g_n_3eqtri (syn_cin A (syn_ccompl A)) (syn_ccompl (syn_cnin A (syn_ccompl A))) (syn_ccompl (syn_cvv)) (syn_c0) p0000 p0002 p0003
  exact p0004

noncomputable def g_uncompl
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cun A (syn_ccompl A)) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_cun] using (Nominal.classEqRefl (syn_cun A (syn_ccompl A))))
  have p0001 :=
    @g_nincompl (syn_ccompl A)
  have p0002 :=
    @g_eqtri (syn_cun A (syn_ccompl A)) (syn_cnin (syn_ccompl A) (syn_ccompl (syn_ccompl A))) (syn_cvv) p0000 p0001
  exact p0002

noncomputable def g_inindif
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cin (syn_cin A B) (syn_cdif A B)) (syn_c0)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    (by simpa [syn_cdif] using (Nominal.classEqRefl (syn_cdif A B)))
  have p0001 :=
    @g_ineq2i (syn_cdif A B) (syn_cin A (syn_ccompl B)) (syn_cin A B) p0000
  have p0002 :=
    @g_inindi A B (syn_ccompl B)
  have p0003 :=
    @g_incompl B
  have p0004 :=
    @g_ineq2i (syn_cin B (syn_ccompl B)) (syn_c0) A p0003
  have p0005 :=
    @g_in0 A
  have p0006 :=
    @g_eqtri (syn_cin A (syn_cin B (syn_ccompl B))) (syn_cin A (syn_c0)) (syn_c0) p0004 p0005
  have p0007 :=
    @g_n_3eqtr2i (syn_cin (syn_cin A B) (syn_cdif A B)) (syn_cin (syn_cin A B) (syn_cin A (syn_ccompl B))) (syn_cin A (syn_cin B (syn_ccompl B))) (syn_c0) p0001 p0002 p0006
  exact p0007

noncomputable def g_ssofss
    (x : Var) (A : Class) (B : Class) (C : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf (.imp (syn_wss A C) (syn_wb (syn_wss A B) (syn_wral x C (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_vex x
  have p0001 :=
    @g_elcompl (.cv x) C p0000
  have p0002 :=
    @g_ssel A C (.cv x)
  have p0003 :=
    @g_con3d (syn_wss A C) (.classMem (.cv x) A) (.classMem (.cv x) C) p0002
  have p0004 :=
    @g_syl5bi (.classMem (.cv x) (syn_ccompl C)) (.neg (.classMem (.cv x) C)) (syn_wss A C) (.neg (.classMem (.cv x) A)) p0001 p0003
  have p0005 :=
    @g_imp (syn_wss A C) (.classMem (.cv x) (syn_ccompl C)) (.neg (.classMem (.cv x) A)) p0004
  have p0006 :=
    @g_pm2_21d (syn_wa (syn_wss A C) (.classMem (.cv x) (syn_ccompl C))) (.classMem (.cv x) A) (.classMem (.cv x) B) p0005
  have p0007 :=
    @g_ralrimiva (syn_wss A C) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) x (syn_ccompl C) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0006
  have p0008 :=
    @g_biantrud (syn_wss A C) (syn_wral x (syn_ccompl C) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) (syn_wral x C (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) p0007
  have p0009 :=
    @g_ralv (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) x
  have p0010 :=
    @g_uncompl C
  have p0011 :=
    @g_raleqi (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) x (syn_cun C (syn_ccompl C)) (syn_cvv) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0010
  have p0012 :=
    @g_dfss2 x A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0013 :=
    @g_n_3bitr4ri (syn_wral x (syn_cvv) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) (syn_wral x (syn_cun C (syn_ccompl C)) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) (syn_wss A B) p0009 p0011 p0012
  have p0014 :=
    @g_ralunb (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) x C (syn_ccompl C)
  have p0015 :=
    @g_bitri (syn_wss A B) (syn_wral x (syn_cun C (syn_ccompl C)) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) (syn_wa (syn_wral x C (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) (syn_wral x (syn_ccompl C) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))) p0013 p0014
  have p0016 :=
    @g_syl6rbbr (syn_wss A C) (syn_wral x C (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) (syn_wa (syn_wral x C (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) (syn_wral x (syn_ccompl C) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))) (syn_wss A B) p0008 p0015
  exact p0016

noncomputable def g_ssofeq
    (x : Var) (A : Class) (B : Class) (C : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wss A C) (syn_wss B C)) (syn_wb (.classEq A B) (syn_wral x C (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_ssofss x A B C (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_ssofss x B A C (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0002 :=
    @g_bi2anan9 (syn_wss A C) (syn_wss A B) (syn_wral x C (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) (syn_wss B C) (syn_wss B A) (syn_wral x C (.imp (.classMem (.cv x) B) (.classMem (.cv x) A))) p0000 p0001
  have p0003 :=
    @g_eqss A B
  have p0004 :=
    @g_ralbiim (.classMem (.cv x) A) (.classMem (.cv x) B) x C
  have p0005 :=
    @g_n_3bitr4g (syn_wa (syn_wss A C) (syn_wss B C)) (syn_wa (syn_wss A B) (syn_wss B A)) (syn_wa (syn_wral x C (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) (syn_wral x C (.imp (.classMem (.cv x) B) (.classMem (.cv x) A)))) (.classEq A B) (syn_wral x C (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B))) p0002 p0003 p0004
  exact p0005

noncomputable def g_axprimlem1
    (B : Class) (a : Var) (c : Var) (dv_B_c : c ∉ B.fv) (dv_a_c : a ≠ c) :
    Nominal.NPrf (syn_wb (.classEq (.cv a) (syn_csn B)) (.all c (syn_wb (.objMem c a) (.classEq (.cv c) B)))) := by
  let proofSupport : Finset Var := B.fv ∪ ({a} : Finset Var) ∪ ({c} : Finset Var)
  have p0000 :=
    @g_dfcleq c (.cv a) (syn_csn B) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_elsn c B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0002 :=
    @g_bibi2i (.classMem (.cv c) (syn_csn B)) (.classEq (.cv c) B) (.objMem c a) p0001
  have p0003 :=
    @g_albii (syn_wb (.objMem c a) (.classMem (.cv c) (syn_csn B))) (syn_wb (.objMem c a) (.classEq (.cv c) B)) c p0002
  have p0004_e00_recanon : Nominal.NPrf (syn_wb (.classEq (.cv a) (syn_csn B)) (.all c (syn_wb (.objMem c a) (.classMem (.cv c) (syn_csn B))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0000
  have p0004 :=
    @g_bitri (.classEq (.cv a) (syn_csn B)) (.all c (syn_wb (.objMem c a) (.classMem (.cv c) (syn_csn B)))) (.all c (syn_wb (.objMem c a) (.classEq (.cv c) B))) p0004_e00_recanon p0003
  exact p0004

noncomputable def g_ninexg
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cnin A B) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_W : x ∉ W.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_W : y ∉ W.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_V : w ∉ V.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_W : w ∉ W.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_V : z ∉ V.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_W : z ∉ W.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_w : x ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_w_ne_z : w ≠ z := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_z_ne_w : z ≠ w :=
    Ne.symm fresh_w_ne_z
  have p0000 :=
    @g_nineq1 (.cv x) A (.cv y)
  have p0001 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_cnin (.cv x) (.cv y)) (syn_cnin A (.cv y)) (syn_cvv) p0000
  have p0002 :=
    @g_nineq2 (.cv y) B A
  have p0003 :=
    @g_eleq1d (.classEq (.cv y) B) (syn_cnin A (.cv y)) (syn_cnin A B) (syn_cvv) p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralBaseFour.axNin x y z w (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0005 :=
    @g_isset z (syn_cnin (.cv x) (.cv y)) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0006 :=
    @g_dfcleq w (.cv z) (syn_cnin (.cv x) (.cv y)) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0007 :=
    @g_vex w
  have p0008 :=
    @g_elnin (.cv w) (.cv x) (.cv y) p0007
  have p0009_e00_recanon : Nominal.NPrf (syn_wb (.classMem (.cv w) (syn_cnin (.cv x) (.cv y))) (syn_wnan (.objMem w x) (.objMem w y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wnan, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0008
  have p0009 :=
    @g_bibi2i (.classMem (.cv w) (syn_cnin (.cv x) (.cv y))) (syn_wnan (.objMem w x) (.objMem w y)) (.objMem w z) p0009_e00_recanon
  have p0010 :=
    @g_albii (syn_wb (.objMem w z) (.classMem (.cv w) (syn_cnin (.cv x) (.cv y)))) (syn_wb (.objMem w z) (syn_wnan (.objMem w x) (.objMem w y))) w p0009
  have p0011_e00_recanon : Nominal.NPrf (syn_wb (.classEq (.cv z) (syn_cnin (.cv x) (.cv y))) (.all w (syn_wb (.objMem w z) (.classMem (.cv w) (syn_cnin (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnin, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0006
  have p0011 :=
    @g_bitri (.classEq (.cv z) (syn_cnin (.cv x) (.cv y))) (.all w (syn_wb (.objMem w z) (.classMem (.cv w) (syn_cnin (.cv x) (.cv y))))) (.all w (syn_wb (.objMem w z) (syn_wnan (.objMem w x) (.objMem w y)))) p0011_e00_recanon p0010
  have p0012 :=
    @g_exbii (.classEq (.cv z) (syn_cnin (.cv x) (.cv y))) (.all w (syn_wb (.objMem w z) (syn_wnan (.objMem w x) (.objMem w y)))) z p0011
  have p0013 :=
    @g_bitri (.classMem (syn_cnin (.cv x) (.cv y)) (syn_cvv)) (syn_wex z (.classEq (.cv z) (syn_cnin (.cv x) (.cv y)))) (syn_wex z (.all w (syn_wb (.objMem w z) (syn_wnan (.objMem w x) (.objMem w y))))) p0005 p0012
  have p0014 :=
    @g_mpbir (.classMem (syn_cnin (.cv x) (.cv y)) (syn_cvv)) (syn_wex z (.all w (syn_wb (.objMem w z) (syn_wnan (.objMem w x) (.objMem w y))))) p0004 p0013
  have p0015 :=
    @g_vtocl2g (.classMem (syn_cnin (.cv x) (.cv y)) (syn_cvv)) (.classMem (syn_cnin A (.cv y)) (syn_cvv)) (.classMem (syn_cnin A B) (syn_cvv)) x y A B V W (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0001 p0003 p0014
  exact p0015

noncomputable def g_complexg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_ccompl A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  have p0000 :=
    (by simpa [syn_ccompl] using (Nominal.classEqRefl (syn_ccompl A)))
  have p0001 :=
    @g_ninexg A A V V
  have p0002 :=
    @g_anidms (.classMem A V) (.classMem (syn_cnin A A) (syn_cvv)) p0001
  have p0003 :=
    @g_syl5eqel (.classMem A V) (syn_ccompl A) (syn_cnin A A) (syn_cvv) p0000 p0002
  exact p0003

noncomputable def g_inexg
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cin A B) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  have p0000 :=
    (by simpa [syn_cin] using (Nominal.classEqRefl (syn_cin A B)))
  have p0001 :=
    @g_ninexg A B V W
  have p0002 :=
    @g_complexg (syn_cnin A B) (syn_cvv)
  have p0003 :=
    @g_syl (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cnin A B) (syn_cvv)) (.classMem (syn_ccompl (syn_cnin A B)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem B W)) (syn_cin A B) (syn_ccompl (syn_cnin A B)) (syn_cvv) p0000 p0003
  exact p0004

noncomputable def g_unexg
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cun A B) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  have p0000 :=
    (by simpa [syn_cun] using (Nominal.classEqRefl (syn_cun A B)))
  have p0001 :=
    @g_complexg A V
  have p0002 :=
    @g_complexg B W
  have p0003 :=
    @g_ninexg (syn_ccompl A) (syn_ccompl B) (syn_cvv) (syn_cvv)
  have p0004 :=
    @g_syl2an (.classMem A V) (.classMem (syn_ccompl A) (syn_cvv)) (.classMem (syn_ccompl B) (syn_cvv)) (.classMem (syn_cnin (syn_ccompl A) (syn_ccompl B)) (syn_cvv)) (.classMem B W) p0001 p0002 p0003
  have p0005 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem B W)) (syn_cun A B) (syn_cnin (syn_ccompl A) (syn_ccompl B)) (syn_cvv) p0000 p0004
  exact p0005

noncomputable def g_difexg
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cdif A B) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  have p0000 :=
    (by simpa [syn_cdif] using (Nominal.classEqRefl (syn_cdif A B)))
  have p0001 :=
    @g_complexg B W
  have p0002 :=
    @g_inexg A (syn_ccompl B) V (syn_cvv)
  have p0003 :=
    @g_sylan2 (.classMem B W) (.classMem A V) (.classMem (syn_ccompl B) (syn_cvv)) (.classMem (syn_cin A (syn_ccompl B)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem B W)) (syn_cdif A B) (syn_cin A (syn_ccompl B)) (syn_cvv) p0000 p0003
  exact p0004

noncomputable def g_symdifexg
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_csymdif A B) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  have p0000 :=
    (by simpa [syn_csymdif] using (Nominal.classEqRefl (syn_csymdif A B)))
  have p0001 :=
    @g_difexg A B V W
  have p0002 :=
    @g_difexg B A W V
  have p0003 :=
    @g_ancoms (.classMem B W) (.classMem A V) (.classMem (syn_cdif B A) (syn_cvv)) p0002
  have p0004 :=
    @g_unexg (syn_cdif A B) (syn_cdif B A) (syn_cvv) (syn_cvv)
  have p0005 :=
    @g_syl2anc (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cdif A B) (syn_cvv)) (.classMem (syn_cdif B A) (syn_cvv)) (.classMem (syn_cun (syn_cdif A B) (syn_cdif B A)) (syn_cvv)) p0001 p0003 p0004
  have p0006 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem B W)) (syn_csymdif A B) (syn_cun (syn_cdif A B) (syn_cdif B A)) (syn_cvv) p0000 p0005
  exact p0006

noncomputable def g_complex
    (A : Class) (hyp_boolex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_ccompl A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_complexg A (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_boolex_1 p0000
  exact p0001

noncomputable def g_inex
    (A : Class) (B : Class) (hyp_boolex_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_boolex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cin A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_inexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem (syn_cin A B) (syn_cvv)) hyp_boolex_1 hyp_boolex_2 p0000
  exact p0001

noncomputable def g_unex
    (A : Class) (B : Class) (hyp_boolex_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_boolex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cun A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_unexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem (syn_cun A B) (syn_cvv)) hyp_boolex_1 hyp_boolex_2 p0000
  exact p0001

noncomputable def g_difex
    (A : Class) (B : Class) (hyp_boolex_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_boolex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cdif A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_difexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem (syn_cdif A B) (syn_cvv)) hyp_boolex_1 hyp_boolex_2 p0000
  exact p0001

noncomputable def g_symdifex
    (A : Class) (B : Class) (hyp_boolex_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_boolex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_csymdif A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_symdifexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem (syn_csymdif A B) (syn_cvv)) hyp_boolex_1 hyp_boolex_2 p0000
  exact p0001

noncomputable def g_vvex
     :
    Nominal.NPrf (.classMem (syn_cvv) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have p0000 :=
    @g_uncompl (.cv x)
  have p0001 :=
    @g_vex x
  have p0002 :=
    @g_complex (.cv x) p0001
  have p0003 :=
    @g_unex (.cv x) (syn_ccompl (.cv x)) p0001 p0002
  have p0004 :=
    @g_eqeltrri (syn_cun (.cv x) (syn_ccompl (.cv x))) (syn_cvv) (syn_cvv) p0000 p0003
  exact p0004

noncomputable def g_n_0ex
     :
    Nominal.NPrf (.classMem (syn_c0) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_complV
  have p0001 :=
    @g_vvex
  have p0002 :=
    @g_complex (syn_cvv) p0001
  have p0003 :=
    @g_eqeltrri (syn_ccompl (syn_cvv)) (syn_c0) (syn_cvv) p0000 p0002
  exact p0003

noncomputable def g_snex
    (A : Class) :
    Nominal.NPrf (.classMem (syn_csn A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have p0000 :=
    @g_sneq (.cv x) A
  have p0001 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_csn (.cv x)) (syn_csn A) (syn_cvv) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralBaseFour.axSn x y z (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_isset y (syn_csn (.cv x)) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0004 :=
    @g_axprimlem1 (.cv x) y z (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0005_e00_recanon : Nominal.NPrf (syn_wb (.classEq (.cv y) (syn_csn (.cv x))) (.all z (syn_wb (.objMem z y) (.objEq z x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0004
  have p0005 :=
    @g_exbii (.classEq (.cv y) (syn_csn (.cv x))) (.all z (syn_wb (.objMem z y) (.objEq z x))) y p0005_e00_recanon
  have p0006 :=
    @g_bitri (.classMem (syn_csn (.cv x)) (syn_cvv)) (syn_wex y (.classEq (.cv y) (syn_csn (.cv x)))) (syn_wex y (.all z (syn_wb (.objMem z y) (.objEq z x)))) p0003 p0005
  have p0007 :=
    @g_mpbir (.classMem (syn_csn (.cv x)) (syn_cvv)) (syn_wex y (.all z (syn_wb (.objMem z y) (.objEq z x)))) p0002 p0006
  have p0008 :=
    @g_vtoclg (.classMem (syn_csn (.cv x)) (syn_cvv)) (.classMem (syn_csn A) (syn_cvv)) x A (syn_cvv) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0001 p0007
  have p0009 :=
    @g_snprc A
  have p0010 :=
    @g_biimpi (.neg (.classMem A (syn_cvv))) (.classEq (syn_csn A) (syn_c0)) p0009
  have p0011 :=
    @g_n_0ex
  have p0012 :=
    @g_syl6eqel (.neg (.classMem A (syn_cvv))) (syn_csn A) (syn_c0) (syn_cvv) p0010 p0011
  have p0013 :=
    @g_pm2_61i (.classMem A (syn_cvv)) (.classMem (syn_csn A) (syn_cvv)) p0008 p0012
  exact p0013

noncomputable def g_prex
    (A : Class) (B : Class) :
    Nominal.NPrf (.classMem (syn_cpr A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    (by simpa [syn_cpr] using (Nominal.classEqRefl (syn_cpr A B)))
  have p0001 :=
    @g_snex A
  have p0002 :=
    @g_snex B
  have p0003 :=
    @g_unex (syn_csn A) (syn_csn B) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_cpr A B) (syn_cun (syn_csn A) (syn_csn B)) (syn_cvv) p0000 p0003
  exact p0004

noncomputable def g_opkex
    (A : Class) (B : Class) :
    Nominal.NPrf (.classMem (syn_copk A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    (by simpa [syn_copk] using (Nominal.classEqRefl (syn_copk A B)))
  have p0001 :=
    @g_prex (syn_csn A) (syn_cpr A B)
  have p0002 :=
    @g_eqeltri (syn_copk A B) (syn_cpr (syn_csn A) (syn_cpr A B)) (syn_cvv) p0000 p0001
  exact p0002

noncomputable def g_snelpwg
    (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (syn_wb (.classMem (syn_csn A) (syn_cpw B)) (.classMem A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv
  have p0000 :=
    @g_snssg A B V
  have p0001 :=
    @g_snex A
  have p0002 :=
    @g_elpw (syn_csn A) B p0001
  have p0003 :=
    @g_syl6rbbr (.classMem A V) (.classMem A B) (syn_wss (syn_csn A) B) (.classMem (syn_csn A) (syn_cpw B)) p0000 p0002
  exact p0003

noncomputable def g_snelpw
    (A : Class) (B : Class) (hyp_snelpw_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_csn A) (syn_cpw B)) (.classMem A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_snelpwg A B (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_snelpw_1 p0000
  exact p0001

noncomputable def g_snelpwi
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem A B) (.classMem (syn_csn A) (syn_cpw B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_snssi A B
  have p0001 :=
    @g_snex A
  have p0002 :=
    @g_elpw (syn_csn A) B p0001
  have p0003 :=
    @g_sylibr (.classMem A B) (syn_wss (syn_csn A) B) (.classMem (syn_csn A) (syn_cpw B)) p0000 p0002
  exact p0003

noncomputable def g_unipw
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cuni (syn_cpw A)) A) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_eluni y (.cv x) (syn_cpw A) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_vex y
  have p0002 :=
    @g_elpw (.cv y) A p0001
  have p0003 :=
    @g_ssel (.cv y) A (.cv x)
  have p0004 :=
    @g_sylbi (.classMem (.cv y) (syn_cpw A)) (syn_wss (.cv y) A) (.imp (.classMem (.cv x) (.cv y)) (.classMem (.cv x) A)) p0002 p0003
  have p0005 :=
    @g_impcom (.classMem (.cv y) (syn_cpw A)) (.classMem (.cv x) (.cv y)) (.classMem (.cv x) A) p0004
  have p0006 :=
    @g_exlimiv (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) (syn_cpw A))) (.classMem (.cv x) A) y (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0005
  have p0007 :=
    @g_sylbi (.classMem (.cv x) (syn_cuni (syn_cpw A))) (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) (syn_cpw A)))) (.classMem (.cv x) A) p0000 p0006
  have p0008 :=
    @g_vex x
  have p0009 :=
    @g_snid (.cv x) p0008
  have p0010 :=
    @g_snelpwi (.cv x) A
  have p0011 :=
    @g_elunii (.cv x) (syn_csn (.cv x)) (syn_cpw A)
  have p0012 :=
    @g_sylancr (.classMem (.cv x) A) (.classMem (.cv x) (syn_csn (.cv x))) (.classMem (syn_csn (.cv x)) (syn_cpw A)) (.classMem (.cv x) (syn_cuni (syn_cpw A))) p0009 p0010 p0011
  have p0013 :=
    @g_impbii (.classMem (.cv x) (syn_cuni (syn_cpw A))) (.classMem (.cv x) A) p0007 p0012
  have p0014 :=
    @g_eqriv x (syn_cuni (syn_cpw A)) A (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0013
  exact p0014

noncomputable def g_sspwb
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wss A B) (syn_wss (syn_cpw A) (syn_cpw B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_sstr2 (.cv x) A B
  have p0001 :=
    @g_com12 (syn_wss (.cv x) A) (syn_wss A B) (syn_wss (.cv x) B) p0000
  have p0002 :=
    @g_vex x
  have p0003 :=
    @g_elpw (.cv x) A p0002
  have p0004 :=
    @g_elpw (.cv x) B p0002
  have p0005 :=
    @g_n_3imtr4g (syn_wss A B) (syn_wss (.cv x) A) (syn_wss (.cv x) B) (.classMem (.cv x) (syn_cpw A)) (.classMem (.cv x) (syn_cpw B)) p0001 p0003 p0004
  have p0006 :=
    @g_ssrdv (syn_wss A B) x (syn_cpw A) (syn_cpw B) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0005
  have p0007 :=
    @g_ssel (syn_cpw A) (syn_cpw B) (syn_csn (.cv x))
  have p0008 :=
    @g_snex (.cv x)
  have p0009 :=
    @g_elpw (syn_csn (.cv x)) A p0008
  have p0010 :=
    @g_snss (.cv x) A p0002
  have p0011 :=
    @g_bitr4i (.classMem (syn_csn (.cv x)) (syn_cpw A)) (syn_wss (syn_csn (.cv x)) A) (.classMem (.cv x) A) p0009 p0010
  have p0012 :=
    @g_elpw (syn_csn (.cv x)) B p0008
  have p0013 :=
    @g_snss (.cv x) B p0002
  have p0014 :=
    @g_bitr4i (.classMem (syn_csn (.cv x)) (syn_cpw B)) (syn_wss (syn_csn (.cv x)) B) (.classMem (.cv x) B) p0012 p0013
  have p0015 :=
    @g_n_3imtr3g (syn_wss (syn_cpw A) (syn_cpw B)) (.classMem (syn_csn (.cv x)) (syn_cpw A)) (.classMem (syn_csn (.cv x)) (syn_cpw B)) (.classMem (.cv x) A) (.classMem (.cv x) B) p0007 p0011 p0014
  have p0016 :=
    @g_ssrdv (syn_wss (syn_cpw A) (syn_cpw B)) x A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0015
  have p0017 :=
    @g_impbii (syn_wss A B) (syn_wss (syn_cpw A) (syn_cpw B)) p0006 p0016
  exact p0017

noncomputable def g_pwadjoin
    (A : Class) (X : Class) (a : Var) (b : Var) (dv_A_a : a ∉ A.fv) (dv_A_b : b ∉ A.fv) (dv_X_a : a ∉ X.fv) (dv_X_b : b ∉ X.fv) (dv_a_b : a ≠ b) :
    Nominal.NPrf (.classEq (syn_cpw (syn_cun A (syn_csn X))) (syn_cun (syn_cpw A) (.cab a (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))))))) := by
  let proofSupport : Finset Var := A.fv ∪ X.fv ∪ ({a} : Finset Var) ∪ ({b} : Finset Var)
  let z : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_X : z ∉ X.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_ne_a : z ≠ a := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_z : a ≠ z :=
    Ne.symm fresh_z_ne_a
  have fresh_z_ne_b : z ≠ b := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_z : b ≠ z :=
    Ne.symm fresh_z_ne_b
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_a : x ≠ a := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_x : b ≠ x :=
    Ne.symm fresh_x_ne_b
  have fresh_z_ne_x : z ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have p0000 :=
    @g_uncom A (syn_csn X)
  have p0001 :=
    @g_sseq2i (syn_cun A (syn_csn X)) (syn_cun (syn_csn X) A) (.cv z) p0000
  have p0002 :=
    @g_ssundif (.cv z) (syn_csn X) A
  have p0003 :=
    @g_bitri (syn_wss (.cv z) (syn_cun A (syn_csn X))) (syn_wss (.cv z) (syn_cun (syn_csn X) A)) (syn_wss (syn_cdif (.cv z) (syn_csn X)) A) p0001 p0002
  have p0004 :=
    @g_biimpi (syn_wss (.cv z) (syn_cun A (syn_csn X))) (syn_wss (syn_cdif (.cv z) (syn_csn X)) A) p0003
  have p0005 :=
    @g_adantr (syn_wss (.cv z) (syn_cun A (syn_csn X))) (syn_wss (syn_cdif (.cv z) (syn_csn X)) A) (.classMem X (.cv z)) p0004
  have p0006 :=
    @g_vex z
  have p0007 :=
    @g_snex X
  have p0008 :=
    @g_difex (.cv z) (syn_csn X) p0006 p0007
  have p0009 :=
    @g_elpw (syn_cdif (.cv z) (syn_csn X)) A p0008
  have p0010 :=
    @g_sylibr (syn_wa (syn_wss (.cv z) (syn_cun A (syn_csn X))) (.classMem X (.cv z))) (syn_wss (syn_cdif (.cv z) (syn_csn X)) A) (.classMem (syn_cdif (.cv z) (syn_csn X)) (syn_cpw A)) p0005 p0009
  have p0011 :=
    @g_difsnid (.cv z) X
  have p0012 :=
    @g_eqcomd (.classMem X (.cv z)) (syn_cun (syn_cdif (.cv z) (syn_csn X)) (syn_csn X)) (.cv z) p0011
  have p0013 :=
    @g_adantl (.classMem X (.cv z)) (.classEq (.cv z) (syn_cun (syn_cdif (.cv z) (syn_csn X)) (syn_csn X))) (syn_wss (.cv z) (syn_cun A (syn_csn X))) p0012
  have p0014 :=
    @g_uneq1 (.cv b) (syn_cdif (.cv z) (syn_csn X)) (syn_csn X)
  have p0015 :=
    @g_eqeq2d (.classEq (.cv b) (syn_cdif (.cv z) (syn_csn X))) (syn_cun (.cv b) (syn_csn X)) (syn_cun (syn_cdif (.cv z) (syn_csn X)) (syn_csn X)) (.cv z) p0014
  have p0016 :=
    @g_rspcev (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X))) (.classEq (.cv z) (syn_cun (syn_cdif (.cv z) (syn_csn X)) (syn_csn X))) b (syn_cdif (.cv z) (syn_csn X)) (syn_cpw A) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0015
  have p0017 :=
    @g_syl2anc (syn_wa (syn_wss (.cv z) (syn_cun A (syn_csn X))) (.classMem X (.cv z))) (.classMem (syn_cdif (.cv z) (syn_csn X)) (syn_cpw A)) (.classEq (.cv z) (syn_cun (syn_cdif (.cv z) (syn_csn X)) (syn_csn X))) (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X)))) p0010 p0013 p0016
  have p0018 :=
    @g_ex (syn_wss (.cv z) (syn_cun A (syn_csn X))) (.classMem X (.cv z)) (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X)))) p0017
  have p0019 :=
    @g_con3d (syn_wss (.cv z) (syn_cun A (syn_csn X))) (.classMem X (.cv z)) (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X)))) p0018
  have p0020 :=
    @g_ssel (.cv z) (syn_cun A (syn_csn X)) (.cv x)
  have p0021_e00_recanon : Nominal.NPrf (.imp (syn_wss (.cv z) (syn_cun A (syn_csn X))) (.imp (.objMem x z) (.classMem (.cv x) (syn_cun A (syn_csn X))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cun syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0020
  have p0021 :=
    @g_com12 (syn_wss (.cv z) (syn_cun A (syn_csn X))) (.objMem x z) (.classMem (.cv x) (syn_cun A (syn_csn X))) p0021_e00_recanon
  have p0022 :=
    @g_elun (.cv x) A (syn_csn X)
  have p0023 :=
    @g_elsn x X (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0024 :=
    @g_orbi2i (.classMem (.cv x) (syn_csn X)) (.classEq (.cv x) X) (.classMem (.cv x) A) p0023
  have p0025 :=
    @g_bitri (.classMem (.cv x) (syn_cun A (syn_csn X))) (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) (syn_csn X))) (syn_wo (.classMem (.cv x) A) (.classEq (.cv x) X)) p0022 p0024
  have p0026 :=
    Nominal.ax1 (.classMem (.cv x) A) (syn_wa (.objMem x z) (.neg (.classMem X (.cv z))))
  have p0027 :=
    @g_eleq1 (.cv x) X (.cv z)
  have p0028_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv x) X) (syn_wb (.objMem x z) (.classMem X (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
      )
      p0027
  have p0028 :=
    @g_anbi1d (.classEq (.cv x) X) (.objMem x z) (.classMem X (.cv z)) (.neg (.classMem X (.cv z))) p0028_e00_recanon
  have p0029 :=
    @g_pm2_21 (.classMem X (.cv z)) (.classMem (.cv x) A)
  have p0030 :=
    @g_impcom (.neg (.classMem X (.cv z))) (.classMem X (.cv z)) (.classMem (.cv x) A) p0029
  have p0031 :=
    @g_syl6bi (.classEq (.cv x) X) (syn_wa (.objMem x z) (.neg (.classMem X (.cv z)))) (syn_wa (.classMem X (.cv z)) (.neg (.classMem X (.cv z)))) (.classMem (.cv x) A) p0028 p0030
  have p0032 :=
    @g_jaoi (.classMem (.cv x) A) (.imp (syn_wa (.objMem x z) (.neg (.classMem X (.cv z)))) (.classMem (.cv x) A)) (.classEq (.cv x) X) p0026 p0031
  have p0033 :=
    @g_sylbi (.classMem (.cv x) (syn_cun A (syn_csn X))) (syn_wo (.classMem (.cv x) A) (.classEq (.cv x) X)) (.imp (syn_wa (.objMem x z) (.neg (.classMem X (.cv z)))) (.classMem (.cv x) A)) p0025 p0032
  have p0034 :=
    @g_exp3a (.classMem (.cv x) (syn_cun A (syn_csn X))) (.objMem x z) (.neg (.classMem X (.cv z))) (.classMem (.cv x) A) p0033
  have p0035 :=
    @g_com12 (.classMem (.cv x) (syn_cun A (syn_csn X))) (.objMem x z) (.imp (.neg (.classMem X (.cv z))) (.classMem (.cv x) A)) p0034
  have p0036 :=
    @g_syld (.objMem x z) (syn_wss (.cv z) (syn_cun A (syn_csn X))) (.classMem (.cv x) (syn_cun A (syn_csn X))) (.imp (.neg (.classMem X (.cv z))) (.classMem (.cv x) A)) p0021 p0035
  have p0037 :=
    @g_imp3a (.objMem x z) (syn_wss (.cv z) (syn_cun A (syn_csn X))) (.neg (.classMem X (.cv z))) (.classMem (.cv x) A) p0036
  have p0038 :=
    @g_com12 (.objMem x z) (syn_wa (syn_wss (.cv z) (syn_cun A (syn_csn X))) (.neg (.classMem X (.cv z)))) (.classMem (.cv x) A) p0037
  have p0039_e00_recanon : Nominal.NPrf (.imp (syn_wa (syn_wss (.cv z) (syn_cun A (syn_csn X))) (.neg (.classMem X (.cv z)))) (.imp (.classMem (.cv x) (.cv z)) (.classMem (.cv x) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_cun syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0038
  have p0039 :=
    @g_ssrdv (syn_wa (syn_wss (.cv z) (syn_cun A (syn_csn X))) (.neg (.classMem X (.cv z)))) x (.cv z) A (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0039_e00_recanon
  have p0040 :=
    @g_ex (syn_wss (.cv z) (syn_cun A (syn_csn X))) (.neg (.classMem X (.cv z))) (syn_wss (.cv z) A) p0039
  have p0041 :=
    @g_syld (syn_wss (.cv z) (syn_cun A (syn_csn X))) (.neg (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X))))) (.neg (.classMem X (.cv z))) (syn_wss (.cv z) A) p0019 p0040
  have p0042 :=
    @g_orrd (syn_wss (.cv z) (syn_cun A (syn_csn X))) (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X)))) (syn_wss (.cv z) A) p0041
  have p0043 :=
    @g_orcomd (syn_wss (.cv z) (syn_cun A (syn_csn X))) (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X)))) (syn_wss (.cv z) A) p0042
  have p0044 :=
    @g_ssun3 (.cv z) A (syn_csn X)
  have p0045 :=
    @g_vex b
  have p0046 :=
    @g_elpw (.cv b) A p0045
  have p0047 :=
    @g_unss1 (.cv b) A (syn_csn X)
  have p0048 :=
    @g_sylbi (.classMem (.cv b) (syn_cpw A)) (syn_wss (.cv b) A) (syn_wss (syn_cun (.cv b) (syn_csn X)) (syn_cun A (syn_csn X))) p0046 p0047
  have p0049 :=
    @g_sseq1 (.cv z) (syn_cun (.cv b) (syn_csn X)) (syn_cun A (syn_csn X))
  have p0050 :=
    @g_syl5ibrcom (.classMem (.cv b) (syn_cpw A)) (syn_wss (.cv z) (syn_cun A (syn_csn X))) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X))) (syn_wss (syn_cun (.cv b) (syn_csn X)) (syn_cun A (syn_csn X))) p0048 p0049
  have p0051 :=
    @g_rexlimiv (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X))) (syn_wss (.cv z) (syn_cun A (syn_csn X))) b (syn_cpw A) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0050
  have p0052 :=
    @g_jaoi (syn_wss (.cv z) A) (syn_wss (.cv z) (syn_cun A (syn_csn X))) (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X)))) p0044 p0051
  have p0053 :=
    @g_impbii (syn_wss (.cv z) (syn_cun A (syn_csn X))) (syn_wo (syn_wss (.cv z) A) (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X))))) p0043 p0052
  have p0054 :=
    @g_elpw (.cv z) (syn_cun A (syn_csn X)) p0006
  have p0055 :=
    @g_elun (.cv z) (syn_cpw A) (.cab a (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X)))))
  have p0056 :=
    @g_elpw (.cv z) A p0006
  have p0057 :=
    @g_eqeq1 (.cv a) (.cv z) (syn_cun (.cv b) (syn_csn X))
  have p0058_e00_recanon : Nominal.NPrf (.imp (.objEq a z) (syn_wb (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0057
  have p0058 :=
    @g_rexbidv (.objEq a z) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X))) b (syn_cpw A) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0058_e00_recanon
  have p0059_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv a) (.cv z)) (syn_wb (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X)))) (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa syn_cpw syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_cun syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0058
  have p0059 :=
    @g_elab (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X)))) (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X)))) a (.cv z) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0006 p0059_e01_recanon
  have p0060 :=
    @g_orbi12i (.classMem (.cv z) (syn_cpw A)) (syn_wss (.cv z) A) (.classMem (.cv z) (.cab a (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X)))))) (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X)))) p0056 p0059
  have p0061 :=
    @g_bitri (.classMem (.cv z) (syn_cun (syn_cpw A) (.cab a (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))))))) (syn_wo (.classMem (.cv z) (syn_cpw A)) (.classMem (.cv z) (.cab a (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))))))) (syn_wo (syn_wss (.cv z) A) (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X))))) p0055 p0060
  have p0062 :=
    @g_n_3bitr4i (syn_wss (.cv z) (syn_cun A (syn_csn X))) (syn_wo (syn_wss (.cv z) A) (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X))))) (.classMem (.cv z) (syn_cpw (syn_cun A (syn_csn X)))) (.classMem (.cv z) (syn_cun (syn_cpw A) (.cab a (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))))))) p0053 p0054 p0061
  have p0063 :=
    @g_eqriv z (syn_cpw (syn_cun A (syn_csn X))) (syn_cun (syn_cpw A) (.cab a (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X)))))) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0062
  exact p0063

noncomputable def g_preqr1
    (A : Class) (B : Class) (C : Class) (hyp_preqr1_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_preqr1_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (.classEq (syn_cpr A C) (syn_cpr B C)) (.classEq A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_prid1 A C hyp_preqr1_1
  have p0001 :=
    @g_eleq2 (syn_cpr A C) (syn_cpr B C) A
  have p0002 :=
    @g_mpbii (.classEq (syn_cpr A C) (syn_cpr B C)) (.classMem A (syn_cpr A C)) (.classMem A (syn_cpr B C)) p0000 p0001
  have p0003 :=
    @g_elpr A B C hyp_preqr1_1
  have p0004 :=
    @g_sylib (.classEq (syn_cpr A C) (syn_cpr B C)) (.classMem A (syn_cpr B C)) (syn_wo (.classEq A B) (.classEq A C)) p0002 p0003
  have p0005 :=
    @g_prid1 B C hyp_preqr1_2
  have p0006 :=
    @g_eleq2 (syn_cpr A C) (syn_cpr B C) B
  have p0007 :=
    @g_mpbiri (.classEq (syn_cpr A C) (syn_cpr B C)) (.classMem B (syn_cpr A C)) (.classMem B (syn_cpr B C)) p0005 p0006
  have p0008 :=
    @g_elpr B A C hyp_preqr1_2
  have p0009 :=
    @g_sylib (.classEq (syn_cpr A C) (syn_cpr B C)) (.classMem B (syn_cpr A C)) (syn_wo (.classEq B A) (.classEq B C)) p0007 p0008
  have p0010 :=
    @g_eqcom A B
  have p0011 :=
    @g_eqeq2 A C B
  have p0012 :=
    @g_oplem1 (.classEq (syn_cpr A C) (syn_cpr B C)) (.classEq A B) (.classEq A C) (.classEq B A) (.classEq B C) p0004 p0009 p0010 p0011
  exact p0012

noncomputable def g_preqr2
    (A : Class) (B : Class) (C : Class) (hyp_preqr2_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_preqr2_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (.classEq (syn_cpr C A) (syn_cpr C B)) (.classEq A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_prcom C A
  have p0001 :=
    @g_prcom C B
  have p0002 :=
    @g_eqeq12i (syn_cpr C A) (syn_cpr A C) (syn_cpr C B) (syn_cpr B C) p0000 p0001
  have p0003 :=
    @g_preqr1 A B C hyp_preqr2_1 hyp_preqr2_2
  have p0004 :=
    @g_sylbi (.classEq (syn_cpr C A) (syn_cpr C B)) (.classEq (syn_cpr A C) (syn_cpr B C)) (.classEq A B) p0002 p0003
  exact p0004

noncomputable def g_preqr2g
    (A : Class) (B : Class) (C : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (.imp (.classEq (syn_cpr C A) (syn_cpr C B)) (.classEq A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_W : x ∉ W.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_W : y ∉ W.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_preq2 (.cv x) A C
  have p0001 :=
    @g_eqeq1d (.classEq (.cv x) A) (syn_cpr C (.cv x)) (syn_cpr C A) (syn_cpr C (.cv y)) p0000
  have p0002 :=
    @g_eqeq1 (.cv x) A (.cv y)
  have p0003_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb (.objEq x y) (.classEq A (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0002
  have p0003 :=
    @g_imbi12d (.classEq (.cv x) A) (.classEq (syn_cpr C (.cv x)) (syn_cpr C (.cv y))) (.classEq (syn_cpr C A) (syn_cpr C (.cv y))) (.objEq x y) (.classEq A (.cv y)) p0001 p0003_e01_recanon
  have p0004 :=
    @g_preq2 (.cv y) B C
  have p0005 :=
    @g_eqeq2d (.classEq (.cv y) B) (syn_cpr C (.cv y)) (syn_cpr C B) (syn_cpr C A) p0004
  have p0006 :=
    @g_eqeq2 (.cv y) B A
  have p0007 :=
    @g_imbi12d (.classEq (.cv y) B) (.classEq (syn_cpr C A) (syn_cpr C (.cv y))) (.classEq (syn_cpr C A) (syn_cpr C B)) (.classEq A (.cv y)) (.classEq A B) p0005 p0006
  have p0008 :=
    @g_vex x
  have p0009 :=
    @g_vex y
  have p0010 :=
    @g_preqr2 (.cv x) (.cv y) C p0008 p0009
  have p0011_e02_recanon : Nominal.NPrf (.imp (.classEq (syn_cpr C (.cv x)) (syn_cpr C (.cv y))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0010
  have p0011 :=
    @g_vtocl2g (.imp (.classEq (syn_cpr C (.cv x)) (syn_cpr C (.cv y))) (.objEq x y)) (.imp (.classEq (syn_cpr C A) (syn_cpr C (.cv y))) (.classEq A (.cv y))) (.imp (.classEq (syn_cpr C A) (syn_cpr C B)) (.classEq A B)) x y A B V W (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0003 p0007 p0011_e02_recanon
  exact p0011

noncomputable def g_elopk
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (syn_wb (.classMem A (syn_copk B C)) (syn_wo (.classEq A (syn_csn B)) (.classEq A (syn_cpr B C)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    (by simpa [syn_copk] using (Nominal.classEqRefl (syn_copk B C)))
  have p0001 :=
    @g_eleq2i (syn_copk B C) (syn_cpr (syn_csn B) (syn_cpr B C)) A p0000
  have p0002 :=
    @g_snex B
  have p0003 :=
    @g_prex B C
  have p0004 :=
    @g_elpr2 A (syn_csn B) (syn_cpr B C) p0002 p0003
  have p0005 :=
    @g_bitri (.classMem A (syn_copk B C)) (.classMem A (syn_cpr (syn_csn B) (syn_cpr B C))) (syn_wo (.classEq A (syn_csn B)) (.classEq A (syn_cpr B C))) p0001 p0004
  exact p0005

noncomputable def g_opkth1g
    (A : Class) (B : Class) (C : Class) (D : Class) (V : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classEq (syn_copk A B) (syn_copk C D))) (.classEq A C)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ V.fv
  have p0000 :=
    @g_eqid (syn_csn C)
  have p0001 :=
    @g_orci (.classEq (syn_csn C) (syn_csn C)) (.classEq (syn_csn C) (syn_cpr C D)) p0000
  have p0002 :=
    @g_elopk (syn_csn C) C D
  have p0003 :=
    @g_mpbir (.classMem (syn_csn C) (syn_copk C D)) (syn_wo (.classEq (syn_csn C) (syn_csn C)) (.classEq (syn_csn C) (syn_cpr C D))) p0001 p0002
  have p0004 :=
    @g_eleq2 (syn_copk A B) (syn_copk C D) (syn_csn C)
  have p0005 :=
    @g_biimprd (.classEq (syn_copk A B) (syn_copk C D)) (.classMem (syn_csn C) (syn_copk A B)) (.classMem (syn_csn C) (syn_copk C D)) p0004
  have p0006 :=
    @g_elopk (syn_csn C) A B
  have p0007 :=
    @g_snidg A V
  have p0008 :=
    @g_eleq2 (syn_csn C) (syn_csn A) A
  have p0009 :=
    @g_syl5ibrcom (.classMem A V) (.classMem A (syn_csn C)) (.classEq (syn_csn C) (syn_csn A)) (.classMem A (syn_csn A)) p0007 p0008
  have p0010 :=
    @g_prid1g A B V
  have p0011 :=
    @g_eleq2 (syn_csn C) (syn_cpr A B) A
  have p0012 :=
    @g_syl5ibrcom (.classMem A V) (.classMem A (syn_csn C)) (.classEq (syn_csn C) (syn_cpr A B)) (.classMem A (syn_cpr A B)) p0010 p0011
  have p0013 :=
    @g_jaod (.classMem A V) (.classEq (syn_csn C) (syn_csn A)) (.classMem A (syn_csn C)) (.classEq (syn_csn C) (syn_cpr A B)) p0009 p0012
  have p0014 :=
    @g_syl5bi (.classMem (syn_csn C) (syn_copk A B)) (syn_wo (.classEq (syn_csn C) (syn_csn A)) (.classEq (syn_csn C) (syn_cpr A B))) (.classMem A V) (.classMem A (syn_csn C)) p0006 p0013
  have p0015 :=
    @g_sylan9r (.classEq (syn_copk A B) (syn_copk C D)) (.classMem (syn_csn C) (syn_copk C D)) (.classMem (syn_csn C) (syn_copk A B)) (.classMem A V) (.classMem A (syn_csn C)) p0005 p0014
  have p0016 :=
    @g_mpi (syn_wa (.classMem A V) (.classEq (syn_copk A B) (syn_copk C D))) (.classMem (syn_csn C) (syn_copk C D)) (.classMem A (syn_csn C)) p0003 p0015
  have p0017 :=
    @g_elsncg A C V
  have p0018 :=
    @g_adantr (.classMem A V) (syn_wb (.classMem A (syn_csn C)) (.classEq A C)) (.classEq (syn_copk A B) (syn_copk C D)) p0017
  have p0019 :=
    @g_mpbid (syn_wa (.classMem A V) (.classEq (syn_copk A B) (syn_copk C D))) (.classMem A (syn_csn C)) (.classEq A C) p0016 p0018
  exact p0019

noncomputable def g_opkthg
    (A : Class) (B : Class) (C : Class) (D : Class) (T : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem A V) (.classMem B W) (.classMem D T)) (syn_wb (.classEq (syn_copk A B) (syn_copk C D)) (syn_wa (.classEq A C) (.classEq B D)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ T.fv ∪ V.fv ∪ W.fv
  have p0000 :=
    @g_simp1 (.classMem A V) (.classMem B W) (.classMem D T)
  have p0001 :=
    @g_opkth1g A B C D V
  have p0002 :=
    @g_sylan (syn_w3a (.classMem A V) (.classMem B W) (.classMem D T)) (.classMem A V) (.classEq (syn_copk A B) (syn_copk C D)) (.classEq A C) p0000 p0001
  have p0003 :=
    @g_simp2 (.classMem A V) (.classMem B W) (.classMem D T)
  have p0004 :=
    @g_simp3 (.classMem A V) (.classMem B W) (.classMem D T)
  have p0005 :=
    @g_jca (syn_w3a (.classMem A V) (.classMem B W) (.classMem D T)) (.classMem B W) (.classMem D T) p0003 p0004
  have p0006 :=
    @g_opkeq1 A C B
  have p0007 :=
    @g_eqeq1d (.classEq A C) (syn_copk A B) (syn_copk C B) (syn_copk C D) p0006
  have p0008 :=
    @g_biimpd (.classEq A C) (.classEq (syn_copk A B) (syn_copk C D)) (.classEq (syn_copk C B) (syn_copk C D)) p0007
  have p0009 :=
    @g_impcom (.classEq A C) (.classEq (syn_copk A B) (syn_copk C D)) (.classEq (syn_copk C B) (syn_copk C D)) p0008
  have p0010 :=
    (by simpa [syn_copk] using (Nominal.classEqRefl (syn_copk C B)))
  have p0011 :=
    (by simpa [syn_copk] using (Nominal.classEqRefl (syn_copk C D)))
  have p0012 :=
    @g_eqeq12i (syn_copk C B) (syn_cpr (syn_csn C) (syn_cpr C B)) (syn_copk C D) (syn_cpr (syn_csn C) (syn_cpr C D)) p0010 p0011
  have p0013 :=
    @g_prex C B
  have p0014 :=
    @g_prex C D
  have p0015 :=
    @g_preqr2 (syn_cpr C B) (syn_cpr C D) (syn_csn C) p0013 p0014
  have p0016 :=
    @g_sylbi (.classEq (syn_copk C B) (syn_copk C D)) (.classEq (syn_cpr (syn_csn C) (syn_cpr C B)) (syn_cpr (syn_csn C) (syn_cpr C D))) (.classEq (syn_cpr C B) (syn_cpr C D)) p0012 p0015
  have p0017 :=
    @g_preqr2g B D C W T
  have p0018 :=
    @g_syl5 (.classEq (syn_copk C B) (syn_copk C D)) (.classEq (syn_cpr C B) (syn_cpr C D)) (syn_wa (.classMem B W) (.classMem D T)) (.classEq B D) p0016 p0017
  have p0019 :=
    @g_syl5 (syn_wa (.classEq (syn_copk A B) (syn_copk C D)) (.classEq A C)) (.classEq (syn_copk C B) (syn_copk C D)) (syn_wa (.classMem B W) (.classMem D T)) (.classEq B D) p0009 p0018
  have p0020 :=
    @g_exp3a (syn_wa (.classMem B W) (.classMem D T)) (.classEq (syn_copk A B) (syn_copk C D)) (.classEq A C) (.classEq B D) p0019
  have p0021 :=
    @g_imp (syn_wa (.classMem B W) (.classMem D T)) (.classEq (syn_copk A B) (syn_copk C D)) (.imp (.classEq A C) (.classEq B D)) p0020
  have p0022 :=
    @g_sylan (syn_w3a (.classMem A V) (.classMem B W) (.classMem D T)) (syn_wa (.classMem B W) (.classMem D T)) (.classEq (syn_copk A B) (syn_copk C D)) (.imp (.classEq A C) (.classEq B D)) p0005 p0021
  have p0023 :=
    @g_jcai (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classMem D T)) (.classEq (syn_copk A B) (syn_copk C D))) (.classEq A C) (.classEq B D) p0002 p0022
  have p0024 :=
    @g_ex (syn_w3a (.classMem A V) (.classMem B W) (.classMem D T)) (.classEq (syn_copk A B) (syn_copk C D)) (syn_wa (.classEq A C) (.classEq B D)) p0023
  have p0025 :=
    @g_opkeq12 A B C D
  have p0026 :=
    @g_impbid1 (syn_w3a (.classMem A V) (.classMem B W) (.classMem D T)) (.classEq (syn_copk A B) (syn_copk C D)) (syn_wa (.classEq A C) (.classEq B D)) p0024 p0025
  exact p0026

noncomputable def g_el1c
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_c1c)) (syn_wex x (.classEq A (syn_csn (.cv x))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_elex A (syn_c1c)
  have p0001 :=
    @g_snex (.cv x)
  have p0002 :=
    @g_eleq1 A (syn_csn (.cv x)) (syn_cvv)
  have p0003 :=
    @g_mpbiri (.classEq A (syn_csn (.cv x))) (.classMem A (syn_cvv)) (.classMem (syn_csn (.cv x)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_exlimiv (.classEq A (syn_csn (.cv x))) (.classMem A (syn_cvv)) x (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0003
  have p0005 :=
    @g_eqeq1 (.cv y) A (syn_csn (.cv x))
  have p0006 :=
    @g_exbidv (.classEq (.cv y) A) (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv x))) x (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_1c y x (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0008 :=
    @g_elab2g (syn_wex x (.classEq (.cv y) (syn_csn (.cv x)))) (syn_wex x (.classEq A (syn_csn (.cv x)))) y A (syn_c1c) (syn_cvv) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0006 p0007
  have p0009 :=
    @g_pm5_21nii (.classMem A (syn_c1c)) (.classMem A (syn_cvv)) (syn_wex x (.classEq A (syn_csn (.cv x)))) p0000 p0004 p0008
  exact p0009

noncomputable def g_snel1c
    (A : Class) (hyp_snel1c_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_csn A) (syn_c1c)) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have p0000 :=
    @g_eqid (syn_csn A)
  have p0001 :=
    @g_sneq (.cv x) A
  have p0002 :=
    @g_eqeq2d (.classEq (.cv x) A) (syn_csn (.cv x)) (syn_csn A) (syn_csn A) p0001
  have p0003 :=
    @g_spcev (.classEq (syn_csn A) (syn_csn (.cv x))) (.classEq (syn_csn A) (syn_csn A)) x A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) hyp_snel1c_1 p0002
  have p0004 :=
    Nominal.mp p0000 p0003
  have p0005 :=
    @g_el1c x (syn_csn A) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0006 :=
    @g_mpbir (.classMem (syn_csn A) (syn_c1c)) (syn_wex x (.classEq (syn_csn A) (syn_csn (.cv x)))) p0004 p0005
  exact p0006

noncomputable def g_snel1cg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_csn A) (syn_c1c))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_sneq (.cv x) A
  have p0001 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_csn (.cv x)) (syn_csn A) (syn_c1c) p0000
  have p0002 :=
    @g_vex x
  have p0003 :=
    @g_snel1c (.cv x) p0002
  have p0004 :=
    @g_vtoclg (.classMem (syn_csn (.cv x)) (syn_c1c)) (.classMem (syn_csn A) (syn_c1c)) x A V (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0001 p0003
  exact p0004

noncomputable def g_n_1cex
     :
    Nominal.NPrf (.classMem (syn_c1c) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_x_ne_w : x ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_w_ne_z : w ≠ z := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_z_ne_w : z ≠ w :=
    Ne.symm fresh_w_ne_z
  have p0000 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralBaseFour.ax1c x y z w (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_isset x (syn_c1c) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_1c y z (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_eqeq2i (syn_c1c) (.cab y (syn_wex z (.classEq (.cv y) (syn_csn (.cv z))))) (.cv x) p0002
  have p0004 :=
    @g_eqabb (syn_wex z (.classEq (.cv y) (syn_csn (.cv z)))) y (.cv x) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0005_e01_recanon : Nominal.NPrf (syn_wb (.classEq (.cv x) (.cab y (syn_wex z (.classEq (.cv y) (syn_csn (.cv z)))))) (.all y (syn_wb (.objMem y x) (syn_wex z (.classEq (.cv y) (syn_csn (.cv z))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0004
  have p0005 :=
    @g_bitri (.classEq (.cv x) (syn_c1c)) (.classEq (.cv x) (.cab y (syn_wex z (.classEq (.cv y) (syn_csn (.cv z)))))) (.all y (syn_wb (.objMem y x) (syn_wex z (.classEq (.cv y) (syn_csn (.cv z)))))) p0003 p0005_e01_recanon
  have p0006 :=
    @g_dfcleq w (.cv y) (syn_csn (.cv z)) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn w (.cv z) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0008_e00_recanon : Nominal.NPrf (.classEq (syn_csn (.cv z)) (.cab w (.objEq w z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        ·
          exact Nominal.RecanonTransportDev.TRecanonClass.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonClass.cab
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0007
  have p0008 :=
    @g_eqabri (.objEq w z) w (syn_csn (.cv z)) p0008_e00_recanon
  have p0009 :=
    @g_bibi2i (.classMem (.cv w) (syn_csn (.cv z))) (.objEq w z) (.objMem w y) p0008
  have p0010 :=
    @g_albii (syn_wb (.objMem w y) (.classMem (.cv w) (syn_csn (.cv z)))) (syn_wb (.objMem w y) (.objEq w z)) w p0009
  have p0011_e00_recanon : Nominal.NPrf (syn_wb (.classEq (.cv y) (syn_csn (.cv z))) (.all w (syn_wb (.objMem w y) (.classMem (.cv w) (syn_csn (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0006
  have p0011 :=
    @g_bitri (.classEq (.cv y) (syn_csn (.cv z))) (.all w (syn_wb (.objMem w y) (.classMem (.cv w) (syn_csn (.cv z))))) (.all w (syn_wb (.objMem w y) (.objEq w z))) p0011_e00_recanon p0010
  have p0012 :=
    @g_exbii (.classEq (.cv y) (syn_csn (.cv z))) (.all w (syn_wb (.objMem w y) (.objEq w z))) z p0011
  have p0013 :=
    @g_bibi2i (syn_wex z (.classEq (.cv y) (syn_csn (.cv z)))) (syn_wex z (.all w (syn_wb (.objMem w y) (.objEq w z)))) (.objMem y x) p0012
  have p0014 :=
    @g_albii (syn_wb (.objMem y x) (syn_wex z (.classEq (.cv y) (syn_csn (.cv z))))) (syn_wb (.objMem y x) (syn_wex z (.all w (syn_wb (.objMem w y) (.objEq w z))))) y p0013
  have p0015 :=
    @g_bitri (.classEq (.cv x) (syn_c1c)) (.all y (syn_wb (.objMem y x) (syn_wex z (.classEq (.cv y) (syn_csn (.cv z)))))) (.all y (syn_wb (.objMem y x) (syn_wex z (.all w (syn_wb (.objMem w y) (.objEq w z)))))) p0005 p0014
  have p0016 :=
    @g_exbii (.classEq (.cv x) (syn_c1c)) (.all y (syn_wb (.objMem y x) (syn_wex z (.all w (syn_wb (.objMem w y) (.objEq w z)))))) x p0015
  have p0017 :=
    @g_bitri (.classMem (syn_c1c) (syn_cvv)) (syn_wex x (.classEq (.cv x) (syn_c1c))) (syn_wex x (.all y (syn_wb (.objMem y x) (syn_wex z (.all w (syn_wb (.objMem w y) (.objEq w z))))))) p0001 p0016
  have p0018 :=
    @g_mpbir (.classMem (syn_c1c) (syn_cvv)) (syn_wex x (.all y (syn_wb (.objMem y x) (syn_wex z (.all w (syn_wb (.objMem w y) (.objEq w z))))))) p0000 p0017
  exact p0018

noncomputable def g_pw1eq
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cpw1 A) (syn_cpw1 B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_pweq A B
  have p0001 :=
    @g_ineq1d (.classEq A B) (syn_cpw A) (syn_cpw B) (syn_c1c) p0000
  have p0002 :=
    (by simpa [syn_cpw1] using (Nominal.classEqRefl (syn_cpw1 A)))
  have p0003 :=
    (by simpa [syn_cpw1] using (Nominal.classEqRefl (syn_cpw1 B)))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cin (syn_cpw A) (syn_c1c)) (syn_cin (syn_cpw B) (syn_c1c)) (syn_cpw1 A) (syn_cpw1 B) p0001 p0002 p0003
  exact p0004

noncomputable def g_elpw1
    (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cpw1 B)) (syn_wrex x B (.classEq A (syn_csn (.cv x))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    (by simpa [syn_cpw1] using (Nominal.classEqRefl (syn_cpw1 B)))
  have p0001 :=
    @g_eleq2i (syn_cpw1 B) (syn_cin (syn_cpw B) (syn_c1c)) A p0000
  have p0002 :=
    @g_elin A (syn_cpw B) (syn_c1c)
  have p0003 :=
    @g_bitri (.classMem A (syn_cpw1 B)) (.classMem A (syn_cin (syn_cpw B) (syn_c1c))) (syn_wa (.classMem A (syn_cpw B)) (.classMem A (syn_c1c))) p0001 p0002
  have p0004 :=
    @g_el1c x A (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0005 :=
    @g_anbi2i (.classMem A (syn_c1c)) (syn_wex x (.classEq A (syn_csn (.cv x)))) (.classMem A (syn_cpw B)) p0004
  have p0006 :=
    @g_n_19_42v (.classMem A (syn_cpw B)) (.classEq A (syn_csn (.cv x))) x (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0007 :=
    @g_bitr4i (syn_wa (.classMem A (syn_cpw B)) (.classMem A (syn_c1c))) (syn_wa (.classMem A (syn_cpw B)) (syn_wex x (.classEq A (syn_csn (.cv x))))) (syn_wex x (syn_wa (.classMem A (syn_cpw B)) (.classEq A (syn_csn (.cv x))))) p0005 p0006
  have p0008 :=
    @g_eleq1 A (syn_csn (.cv x)) (syn_cpw B)
  have p0009 :=
    @g_snex (.cv x)
  have p0010 :=
    @g_elpw (syn_csn (.cv x)) B p0009
  have p0011 :=
    @g_vex x
  have p0012 :=
    @g_snss (.cv x) B p0011
  have p0013 :=
    @g_bitr4i (.classMem (syn_csn (.cv x)) (syn_cpw B)) (syn_wss (syn_csn (.cv x)) B) (.classMem (.cv x) B) p0010 p0012
  have p0014 :=
    @g_syl6bb (.classEq A (syn_csn (.cv x))) (.classMem A (syn_cpw B)) (.classMem (syn_csn (.cv x)) (syn_cpw B)) (.classMem (.cv x) B) p0008 p0013
  have p0015 :=
    @g_pm5_32ri (.classEq A (syn_csn (.cv x))) (.classMem A (syn_cpw B)) (.classMem (.cv x) B) p0014
  have p0016 :=
    @g_exbii (syn_wa (.classMem A (syn_cpw B)) (.classEq A (syn_csn (.cv x)))) (syn_wa (.classMem (.cv x) B) (.classEq A (syn_csn (.cv x)))) x p0015
  have p0017 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex x B (.classEq A (syn_csn (.cv x))))))
  have p0018 :=
    @g_bitr4i (syn_wex x (syn_wa (.classMem A (syn_cpw B)) (.classEq A (syn_csn (.cv x))))) (syn_wex x (syn_wa (.classMem (.cv x) B) (.classEq A (syn_csn (.cv x))))) (syn_wrex x B (.classEq A (syn_csn (.cv x)))) p0016 p0017
  have p0019 :=
    @g_bitri (syn_wa (.classMem A (syn_cpw B)) (.classMem A (syn_c1c))) (syn_wex x (syn_wa (.classMem A (syn_cpw B)) (.classEq A (syn_csn (.cv x))))) (syn_wrex x B (.classEq A (syn_csn (.cv x)))) p0007 p0018
  have p0020 :=
    @g_bitri (.classMem A (syn_cpw1 B)) (syn_wa (.classMem A (syn_cpw B)) (.classMem A (syn_c1c))) (syn_wrex x B (.classEq A (syn_csn (.cv x)))) p0003 p0019
  exact p0020

noncomputable def g_elpw12
    (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cpw1 (syn_cpw1 B))) (syn_wrex x B (.classEq A (syn_csn (syn_csn (.cv x)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_elpw1 y A (syn_cpw1 B) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    @g_elpw1 x (.cv y) B (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0002 :=
    @g_anbi1i (.classMem (.cv y) (syn_cpw1 B)) (syn_wrex x B (.classEq (.cv y) (syn_csn (.cv x)))) (.classEq A (syn_csn (.cv y))) p0001
  have p0003 :=
    @g_r19_41v (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y))) x B (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0004 :=
    @g_bitr4i (syn_wa (.classMem (.cv y) (syn_cpw1 B)) (.classEq A (syn_csn (.cv y)))) (syn_wa (syn_wrex x B (.classEq (.cv y) (syn_csn (.cv x)))) (.classEq A (syn_csn (.cv y)))) (syn_wrex x B (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y))))) p0002 p0003
  have p0005 :=
    @g_exbii (syn_wa (.classMem (.cv y) (syn_cpw1 B)) (.classEq A (syn_csn (.cv y)))) (syn_wrex x B (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y))))) y p0004
  have p0006 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y (syn_cpw1 B) (.classEq A (syn_csn (.cv y))))))
  have p0007 :=
    @g_rexcom4 (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y)))) x y B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0008 :=
    @g_n_3bitr4i (syn_wex y (syn_wa (.classMem (.cv y) (syn_cpw1 B)) (.classEq A (syn_csn (.cv y))))) (syn_wex y (syn_wrex x B (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y)))))) (syn_wrex y (syn_cpw1 B) (.classEq A (syn_csn (.cv y)))) (syn_wrex x B (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y)))))) p0005 p0006 p0007
  have p0009 :=
    @g_snex (.cv x)
  have p0010 :=
    @g_sneq (.cv y) (syn_csn (.cv x))
  have p0011 :=
    @g_eqeq2d (.classEq (.cv y) (syn_csn (.cv x))) (syn_csn (.cv y)) (syn_csn (syn_csn (.cv x))) A p0010
  have p0012 :=
    @g_ceqsexv (.classEq A (syn_csn (.cv y))) (.classEq A (syn_csn (syn_csn (.cv x)))) y (syn_csn (.cv x)) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0009 p0011
  have p0013 :=
    @g_rexbii (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y))))) (.classEq A (syn_csn (syn_csn (.cv x)))) x B p0012
  have p0014 :=
    @g_n_3bitri (.classMem A (syn_cpw1 (syn_cpw1 B))) (syn_wrex y (syn_cpw1 B) (.classEq A (syn_csn (.cv y)))) (syn_wrex x B (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y)))))) (syn_wrex x B (.classEq A (syn_csn (syn_csn (.cv x))))) p0000 p0008 p0013
  exact p0014

noncomputable def g_snelpw1
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (.classMem (syn_csn A) (syn_cpw1 B)) (.classMem A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_eqcom (syn_csn A) (syn_csn (.cv x))
  have p0001 :=
    @g_vex x
  have p0002 :=
    @g_sneqb (.cv x) A p0001
  have p0003 :=
    @g_bitri (.classEq (syn_csn A) (syn_csn (.cv x))) (.classEq (syn_csn (.cv x)) (syn_csn A)) (.classEq (.cv x) A) p0000 p0002
  have p0004 :=
    @g_rexbii (.classEq (syn_csn A) (syn_csn (.cv x))) (.classEq (.cv x) A) x B p0003
  have p0005 :=
    @g_elpw1 x (syn_csn A) B (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0006 :=
    @g_risset x A B (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0007 :=
    @g_n_3bitr4i (syn_wrex x B (.classEq (syn_csn A) (syn_csn (.cv x)))) (syn_wrex x B (.classEq (.cv x) A)) (.classMem (syn_csn A) (syn_cpw1 B)) (.classMem A B) p0004 p0005 p0006
  exact p0007

noncomputable def g_elpw11c
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cpw1 (syn_c1c))) (syn_wex x (.classEq A (syn_csn (syn_csn (.cv x)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_elpw1 y A (syn_c1c) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y (syn_c1c) (.classEq A (syn_csn (.cv y))))))
  have p0002 :=
    @g_el1c x (.cv y) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_anbi1i (.classMem (.cv y) (syn_c1c)) (syn_wex x (.classEq (.cv y) (syn_csn (.cv x)))) (.classEq A (syn_csn (.cv y))) p0002
  have p0004 :=
    @g_n_19_41v (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y))) x (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0005 :=
    @g_bitr4i (syn_wa (.classMem (.cv y) (syn_c1c)) (.classEq A (syn_csn (.cv y)))) (syn_wa (syn_wex x (.classEq (.cv y) (syn_csn (.cv x)))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y))))) p0003 p0004
  have p0006 :=
    @g_exbii (syn_wa (.classMem (.cv y) (syn_c1c)) (.classEq A (syn_csn (.cv y)))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y))))) y p0005
  have p0007 :=
    @g_bitri (syn_wrex y (syn_c1c) (.classEq A (syn_csn (.cv y)))) (syn_wex y (syn_wa (.classMem (.cv y) (syn_c1c)) (.classEq A (syn_csn (.cv y))))) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y)))))) p0001 p0006
  have p0008 :=
    @g_excom (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y)))) y x
  have p0009 :=
    @g_snex (.cv x)
  have p0010 :=
    @g_sneq (.cv y) (syn_csn (.cv x))
  have p0011 :=
    @g_eqeq2d (.classEq (.cv y) (syn_csn (.cv x))) (syn_csn (.cv y)) (syn_csn (syn_csn (.cv x))) A p0010
  have p0012 :=
    @g_ceqsexv (.classEq A (syn_csn (.cv y))) (.classEq A (syn_csn (syn_csn (.cv x)))) y (syn_csn (.cv x)) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0009 p0011
  have p0013 :=
    @g_exbii (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y))))) (.classEq A (syn_csn (syn_csn (.cv x)))) x p0012
  have p0014 :=
    @g_bitri (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (.classEq A (syn_csn (syn_csn (.cv x))))) p0008 p0013
  have p0015 :=
    @g_n_3bitri (.classMem A (syn_cpw1 (syn_c1c))) (syn_wrex y (syn_c1c) (.classEq A (syn_csn (.cv y)))) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (.classEq A (syn_csn (syn_csn (.cv x))))) p0000 p0007 p0014
  exact p0015

noncomputable def g_elpw121c
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (.cv x))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_elpw1 y A (syn_cpw1 (syn_c1c)) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y (syn_cpw1 (syn_c1c)) (.classEq A (syn_csn (.cv y))))))
  have p0002 :=
    @g_elpw11c x (.cv y) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_anbi1i (.classMem (.cv y) (syn_cpw1 (syn_c1c))) (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (.cv x))))) (.classEq A (syn_csn (.cv y))) p0002
  have p0004 :=
    @g_n_19_41v (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (.classEq A (syn_csn (.cv y))) x (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0005 :=
    @g_bitr4i (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_c1c))) (.classEq A (syn_csn (.cv y)))) (syn_wa (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (.cv x))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (.classEq A (syn_csn (.cv y))))) p0003 p0004
  have p0006 :=
    @g_exbii (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_c1c))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (.classEq A (syn_csn (.cv y))))) y p0005
  have p0007 :=
    @g_bitri (syn_wrex y (syn_cpw1 (syn_c1c)) (.classEq A (syn_csn (.cv y)))) (syn_wex y (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_c1c))) (.classEq A (syn_csn (.cv y))))) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (.classEq A (syn_csn (.cv y)))))) p0001 p0006
  have p0008 :=
    @g_excom (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (.classEq A (syn_csn (.cv y)))) y x
  have p0009 :=
    @g_snex (syn_csn (.cv x))
  have p0010 :=
    @g_sneq (.cv y) (syn_csn (syn_csn (.cv x)))
  have p0011 :=
    @g_eqeq2d (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_csn (.cv y)) (syn_csn (syn_csn (syn_csn (.cv x)))) A p0010
  have p0012 :=
    @g_ceqsexv (.classEq A (syn_csn (.cv y))) (.classEq A (syn_csn (syn_csn (syn_csn (.cv x))))) y (syn_csn (syn_csn (.cv x))) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0009 p0011
  have p0013 :=
    @g_exbii (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (.classEq A (syn_csn (.cv y))))) (.classEq A (syn_csn (syn_csn (syn_csn (.cv x))))) x p0012
  have p0014 :=
    @g_bitri (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (.cv x)))))) p0008 p0013
  have p0015 :=
    @g_bitri (syn_wrex y (syn_cpw1 (syn_c1c)) (.classEq A (syn_csn (.cv y)))) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (.cv x)))))) p0007 p0014
  have p0016 :=
    @g_bitri (.classMem A (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_wrex y (syn_cpw1 (syn_c1c)) (.classEq A (syn_csn (.cv y)))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (.cv x)))))) p0000 p0015
  exact p0016

noncomputable def g_elpw131c
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_elpw1 y A (syn_cpw1 (syn_cpw1 (syn_c1c))) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classEq A (syn_csn (.cv y))))))
  have p0002 :=
    @g_elpw121c x (.cv y) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_anbi1i (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classEq A (syn_csn (.cv y))) p0002
  have p0004 :=
    @g_n_19_41v (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classEq A (syn_csn (.cv y))) x (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0005 :=
    @g_bitr4i (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classEq A (syn_csn (.cv y)))) (syn_wa (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classEq A (syn_csn (.cv y))))) p0003 p0004
  have p0006 :=
    @g_exbii (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classEq A (syn_csn (.cv y))))) y p0005
  have p0007 :=
    @g_bitri (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classEq A (syn_csn (.cv y)))) (syn_wex y (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classEq A (syn_csn (.cv y))))) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classEq A (syn_csn (.cv y)))))) p0001 p0006
  have p0008 :=
    @g_excom (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classEq A (syn_csn (.cv y)))) y x
  have p0009 :=
    @g_snex (syn_csn (syn_csn (.cv x)))
  have p0010 :=
    @g_sneq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))
  have p0011 :=
    @g_eqeq2d (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_csn (.cv y)) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) A p0010
  have p0012 :=
    @g_ceqsexv (.classEq A (syn_csn (.cv y))) (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) y (syn_csn (syn_csn (syn_csn (.cv x)))) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0009 p0011
  have p0013 :=
    @g_exbii (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classEq A (syn_csn (.cv y))))) (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) x p0012
  have p0014 :=
    @g_bitri (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) p0008 p0013
  have p0015 :=
    @g_bitri (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classEq A (syn_csn (.cv y)))) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) p0007 p0014
  have p0016 :=
    @g_bitri (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) p0000 p0015
  exact p0016

noncomputable def g_elpw141c
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_elpw1 y A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classEq A (syn_csn (.cv y))))))
  have p0002 :=
    @g_elpw131c x (.cv y) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_anbi1i (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) (.classEq A (syn_csn (.cv y))) p0002
  have p0004 :=
    @g_n_19_41v (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classEq A (syn_csn (.cv y))) x (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0005 :=
    @g_bitr4i (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (.classEq A (syn_csn (.cv y)))) (syn_wa (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classEq A (syn_csn (.cv y))))) p0003 p0004
  have p0006 :=
    @g_exbii (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classEq A (syn_csn (.cv y))))) y p0005
  have p0007 :=
    @g_bitri (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classEq A (syn_csn (.cv y)))) (syn_wex y (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (.classEq A (syn_csn (.cv y))))) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classEq A (syn_csn (.cv y)))))) p0001 p0006
  have p0008 :=
    @g_excom (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classEq A (syn_csn (.cv y)))) y x
  have p0009 :=
    @g_snex (syn_csn (syn_csn (syn_csn (.cv x))))
  have p0010 :=
    @g_sneq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
  have p0011 :=
    @g_eqeq2d (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (syn_csn (.cv y)) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) A p0010
  have p0012 :=
    @g_ceqsexv (.classEq A (syn_csn (.cv y))) (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) y (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0009 p0011
  have p0013 :=
    @g_exbii (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classEq A (syn_csn (.cv y))))) (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) x p0012
  have p0014 :=
    @g_bitri (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))) p0008 p0013
  have p0015 :=
    @g_bitri (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classEq A (syn_csn (.cv y)))) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))) p0007 p0014
  have p0016 :=
    @g_bitri (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))) p0000 p0015
  exact p0016

noncomputable def g_elpw151c
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_elpw1 y A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (.classEq A (syn_csn (.cv y))))))
  have p0002 :=
    @g_elpw141c x (.cv y) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_anbi1i (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))) (.classEq A (syn_csn (.cv y))) p0002
  have p0004 :=
    @g_n_19_41v (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) (.classEq A (syn_csn (.cv y))) x (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0005 :=
    @g_bitr4i (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classEq A (syn_csn (.cv y)))) (syn_wa (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) (.classEq A (syn_csn (.cv y))))) p0003 p0004
  have p0006 :=
    @g_exbii (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) (.classEq A (syn_csn (.cv y))))) y p0005
  have p0007 :=
    @g_bitri (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (.classEq A (syn_csn (.cv y)))) (syn_wex y (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classEq A (syn_csn (.cv y))))) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) (.classEq A (syn_csn (.cv y)))))) p0001 p0006
  have p0008 :=
    @g_excom (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) (.classEq A (syn_csn (.cv y)))) y x
  have p0009 :=
    @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
  have p0010 :=
    @g_sneq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
  have p0011 :=
    @g_eqeq2d (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) (syn_csn (.cv y)) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) A p0010
  have p0012 :=
    @g_ceqsexv (.classEq A (syn_csn (.cv y))) (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))) y (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0009 p0011
  have p0013 :=
    @g_exbii (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) (.classEq A (syn_csn (.cv y))))) (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))) x p0012
  have p0014 :=
    @g_bitri (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))) p0008 p0013
  have p0015 :=
    @g_bitri (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (.classEq A (syn_csn (.cv y)))) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))) p0007 p0014
  have p0016 :=
    @g_bitri (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))) p0000 p0015
  exact p0016

noncomputable def g_elpw161c
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_elpw1 y A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classEq A (syn_csn (.cv y))))))
  have p0002 :=
    @g_elpw151c x (.cv y) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_anbi1i (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))) (.classEq A (syn_csn (.cv y))) p0002
  have p0004 :=
    @g_n_19_41v (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))) (.classEq A (syn_csn (.cv y))) x (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0005 :=
    @g_bitr4i (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (.classEq A (syn_csn (.cv y)))) (syn_wa (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))) (.classEq A (syn_csn (.cv y))))) p0003 p0004
  have p0006 :=
    @g_exbii (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))) (.classEq A (syn_csn (.cv y))))) y p0005
  have p0007 :=
    @g_bitri (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classEq A (syn_csn (.cv y)))) (syn_wex y (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (.classEq A (syn_csn (.cv y))))) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))) (.classEq A (syn_csn (.cv y)))))) p0001 p0006
  have p0008 :=
    @g_excom (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))) (.classEq A (syn_csn (.cv y)))) y x
  have p0009 :=
    @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
  have p0010 :=
    @g_sneq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
  have p0011 :=
    @g_eqeq2d (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))) (syn_csn (.cv y)) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))) A p0010
  have p0012 :=
    @g_ceqsexv (.classEq A (syn_csn (.cv y))) (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))) y (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0009 p0011
  have p0013 :=
    @g_exbii (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))) (.classEq A (syn_csn (.cv y))))) (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))) x p0012
  have p0014 :=
    @g_bitri (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))) p0008 p0013
  have p0015 :=
    @g_bitri (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classEq A (syn_csn (.cv y)))) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))) p0007 p0014
  have p0016 :=
    @g_bitri (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))) p0000 p0015
  exact p0016

noncomputable def g_elpw171c
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_elpw1 y A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (.classEq A (syn_csn (.cv y))))))
  have p0002 :=
    @g_elpw161c x (.cv y) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_anbi1i (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))) (.classEq A (syn_csn (.cv y))) p0002
  have p0004 :=
    @g_n_19_41v (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))) (.classEq A (syn_csn (.cv y))) x (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0005 :=
    @g_bitr4i (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (.classEq A (syn_csn (.cv y)))) (syn_wa (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))) (.classEq A (syn_csn (.cv y))))) p0003 p0004
  have p0006 :=
    @g_exbii (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))) (.classEq A (syn_csn (.cv y))))) y p0005
  have p0007 :=
    @g_bitri (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex y (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (.classEq A (syn_csn (.cv y))))) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))) (.classEq A (syn_csn (.cv y)))))) p0001 p0006
  have p0008 :=
    @g_excom (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))) (.classEq A (syn_csn (.cv y)))) y x
  have p0009 :=
    @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
  have p0010 :=
    @g_sneq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))
  have p0011 :=
    @g_eqeq2d (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))) (syn_csn (.cv y)) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))) A p0010
  have p0012 :=
    @g_ceqsexv (.classEq A (syn_csn (.cv y))) (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))) y (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0009 p0011
  have p0013 :=
    @g_exbii (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))) (.classEq A (syn_csn (.cv y))))) (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))) x p0012
  have p0014 :=
    @g_bitri (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))) p0008 p0013
  have p0015 :=
    @g_bitri (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))) p0007 p0014
  have p0016 :=
    @g_bitri (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))) p0000 p0015
  exact p0016

noncomputable def g_elpw181c
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_elpw1 y A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (.classEq A (syn_csn (.cv y))))))
  have p0002 :=
    @g_elpw171c x (.cv y) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_anbi1i (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))) (.classEq A (syn_csn (.cv y))) p0002
  have p0004 :=
    @g_n_19_41v (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))) (.classEq A (syn_csn (.cv y))) x (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0005 :=
    @g_bitr4i (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (.classEq A (syn_csn (.cv y)))) (syn_wa (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))) (.classEq A (syn_csn (.cv y))))) p0003 p0004
  have p0006 :=
    @g_exbii (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))) (.classEq A (syn_csn (.cv y))))) y p0005
  have p0007 :=
    @g_bitri (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex y (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (.classEq A (syn_csn (.cv y))))) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))) (.classEq A (syn_csn (.cv y)))))) p0001 p0006
  have p0008 :=
    @g_excom (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))) (.classEq A (syn_csn (.cv y)))) y x
  have p0009 :=
    @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))
  have p0010 :=
    @g_sneq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
  have p0011 :=
    @g_eqeq2d (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))) (syn_csn (.cv y)) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))) A p0010
  have p0012 :=
    @g_ceqsexv (.classEq A (syn_csn (.cv y))) (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))) y (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0009 p0011
  have p0013 :=
    @g_exbii (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))) (.classEq A (syn_csn (.cv y))))) (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))) x p0012
  have p0014 :=
    @g_bitri (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))) p0008 p0013
  have p0015 :=
    @g_bitri (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))) p0007 p0014
  have p0016 :=
    @g_bitri (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))) p0000 p0015
  exact p0016

noncomputable def g_elpw191c
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_elpw1 y A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (by first | (simp (config := { failIfUnchanged := false }) only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0001 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (.classEq A (syn_csn (.cv y))))))
  have p0002 :=
    @g_elpw181c x (.cv y) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0003 :=
    @g_anbi1i (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))) (.classEq A (syn_csn (.cv y))) p0002
  have p0004 :=
    @g_n_19_41v (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))) (.classEq A (syn_csn (.cv y))) x (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption)
  have p0005 :=
    @g_bitr4i (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (.classEq A (syn_csn (.cv y)))) (syn_wa (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))) (.classEq A (syn_csn (.cv y))))) p0003 p0004
  have p0006 :=
    @g_exbii (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))) (.classEq A (syn_csn (.cv y))))) y p0005
  have p0007 :=
    @g_bitri (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex y (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (.classEq A (syn_csn (.cv y))))) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))) (.classEq A (syn_csn (.cv y)))))) p0001 p0006
  have p0008 :=
    @g_excom (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))) (.classEq A (syn_csn (.cv y)))) y x
  have p0009 :=
    @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
  have p0010 :=
    @g_sneq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))
  have p0011 :=
    @g_eqeq2d (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))) (syn_csn (.cv y)) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))) A p0010
  have p0012 :=
    @g_ceqsexv (.classEq A (syn_csn (.cv y))) (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))) y (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) (by first | (simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.disjoint_left] at ⊢ <;> aesop) | assumption) p0009 p0011
  have p0013 :=
    @g_exbii (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))) (.classEq A (syn_csn (.cv y))))) (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))) x p0012
  have p0014 :=
    @g_bitri (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))) p0008 p0013
  have p0015 :=
    @g_bitri (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))) p0007 p0014
  have p0016 :=
    @g_bitri (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))) p0000 p0015
  exact p0016

#print axioms g_elpw191c

end NFChoice.DirectNominalPrf.WPPReplay
