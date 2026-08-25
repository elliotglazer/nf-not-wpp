import NFStandard.Equivalence
import NFStandard.Consequences
import NFStandard.WPP
import NominalWPPReplayChunk018Compact001
import ReplaySupport.Basic
import WPPCompactSyntaxFVExplicit

namespace NFChoice.Foundation.NFStandard

open scoped Fol
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal.BoundedNominalLoweringBridgeDev004

/- Soundness of the accepted nominal replay, stated at its source WPP. -/
set_option maxRecDepth 30000 in
theorem literalHailperin_valid_not_WPP {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) :
    Wff.Valid S (.neg syn_wwpp) := by
  intro v
  let a : S := v 0
  let rho : Var → Fin 1 := fun _ => 0
  let xs : DVec S 1 := DVec.cons a DVec.nil
  let v0 : Var → S := fun _ => a
  have hprf : Fol.prf LiteralHailperinNF.fst
      (Nominal.lowerWff (finValRho rho) (.neg syn_wwpp)) :=
    NFChoice.DirectNominalPrf.WPPReplay.g_wppfiniteblocknotwppndv
      (finValRho rho)
  have hs : Fol.realize_formula v0
      (Nominal.lowerWff (finValRho rho) (.neg syn_wwpp)) DVec.nil := by
    apply Fol.formula_soundness hprf S v0
    intro f hf
    rcases hf with ⟨g, hg, rfl⟩
    exact (Fol.realize_sentence_iff v0 g).mp (hH hg)
  rw [lowerWff_toFlypitch rho (.neg syn_wwpp)] at hs
  have hv : ∀ k (hk : k < 1), xs.nth k hk = v0 k := by
    intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
    subst k
    simp [xs, v0, a]
  have hb : Fol.realize_bounded_formula xs
      (Formula.toFlypitch (Lowering.lowerWff rho (.neg syn_wwpp)))
      DVec.nil :=
    (Fol.realize_bounded_formula_iff hv _ DVec.nil).2 hs
  have hconst : Wff.Holds S v0 (.neg syn_wwpp) :=
    (Lowering.lowerWff_realize_iff rho xs v0
      (by intro x; simp [rho, xs, v0, a]) (.neg syn_wwpp)).2 hb
  have hagree : AgreesOn (Wff.neg syn_wwpp).fv v0 v := by
    intro x hx
    simp [Wff.neg, Wff.fv, fv_syn_wwpp] at hx
  exact (Wff.holds_congr_fv (.neg syn_wwpp) v0 v hagree).mp hconst

/-- The accepted replay proves the exact lowered WPP sentence from the literal basis. -/
theorem literalHailperin_proves_not_WPP :
    LiteralHailperinNF ⊢ₛ' Fol.bd_not WPP := by
  unfold WPP
  exact NFChoice.ReplaySupport.derives_not_of_nominal_validity
    syn_wwpp WPPSyntax fv_syn_wwpp lowerClosed_syn_wwpp
    (fun _ _ hH => literalHailperin_valid_not_WPP hH)

/- Replace every use of an axiom in a Flypitch derivation by a derivation
of that axiom from a new theory. -/
noncomputable def replacePrfAxioms
    {Γ Δ : Set (Fol.formula LNF)} {f : Fol.formula LNF}
    (hΓ : ∀ ⦃p⦄, p ∈ Γ → Fol.prf Δ p)
    (hf : Fol.prf Γ f) : Fol.prf Δ f := by
  induction hf generalizing Δ with
  | axm h => exact hΓ h
  | impI _ ih =>
      apply Fol.prf.impI
      apply ih
      intro p hp
      exact Classical.choice (show Nonempty (Fol.prf (insert _ Δ) p) from by
        rcases hp with rfl | hp
        · exact ⟨Fol.prf.axm (Set.mem_insert _ _)⟩
        · exact ⟨Fol.weakening (Set.subset_insert _ _) (hΓ hp)⟩)
  | impE A _ _ ih₁ ih₂ => exact Fol.prf.impE A (ih₁ hΓ) (ih₂ hΓ)
  | falsumE _ ih =>
      apply Fol.prf.falsumE
      apply ih
      intro p hp
      exact Classical.choice (show Nonempty (Fol.prf (insert _ Δ) p) from by
        rcases hp with rfl | hp
        · exact ⟨Fol.prf.axm (Set.mem_insert _ _)⟩
        · exact ⟨Fol.weakening (Set.subset_insert _ _) (hΓ hp)⟩)
  | allI _ ih =>
      apply Fol.prf.allI
      apply ih
      intro p hp
      exact Classical.choice (show
          Nonempty (Fol.prf (Fol.lift_formula1 '' Δ) p) from by
        rcases hp with ⟨q, hq, rfl⟩
        exact ⟨Fol.prf_lift 1 0 (hΓ hq)⟩)
  | allE₂ A t _ ih => exact Fol.prf.allE₂ A t (ih hΓ)
  | ref => exact Fol.prf.ref _ _
  | subst₂ s t p _ _ ih₁ ih₂ =>
      exact Fol.prf.subst₂ s t p (ih₁ hΓ) (ih₂ hΓ)

/- The exact identity-environment replay proof, with every finite-basis axiom
replaced by its derivation from standard NF.  This is the public-surface bridge. -/
noncomputable def nfPrfNotSourceWPP :
    Fol.prf NF.fst (Nominal.lowerWff id (Wff.neg syn_wwpp)) :=
  replacePrfAxioms
    (fun p hp => by
      exact Classical.choice (show Nonempty (Fol.prf NF.fst p) from by
        rcases hp with ⟨f, hf, rfl⟩
        rcases hf with ⟨name, rfl⟩
        exact ⟨Classical.choice (literalAxiom_derivable_in_NF name)⟩))
    (NFChoice.DirectNominalPrf.WPPReplay.g_wppfiniteblocknotwppndv id)

/-- The repository's finite presentation proves the negation of WPP. -/
theorem hailperin_proves_not_WPP :
    HailperinNF ⊢ₛ' Fol.bd_not WPP :=
  hailperinPresentation_deductivelyEquivalent.mpr
    literalHailperin_proves_not_WPP

/-- Standard NF proves the negation of WPP, by full finite-basis equivalence. -/
theorem NF_proves_not_WPP : NF ⊢ₛ' Fol.bd_not WPP :=
  nf_hailperin_deductivelyEquivalent.mpr hailperin_proves_not_WPP

#print axioms literalHailperin_valid_not_WPP
#print axioms literalHailperin_proves_not_WPP
#print axioms replacePrfAxioms
#print axioms nfPrfNotSourceWPP
#print axioms hailperin_proves_not_WPP
#print axioms NF_proves_not_WPP

end NFChoice.Foundation.NFStandard
