import NFStandard.Consequences
import NominalWPPReplayChunk018Compact001

namespace NFChoice.Foundation.NFStandard

open scoped Fol
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.DirectNominalPrf

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

#print axioms replacePrfAxioms
#print axioms nfPrfNotSourceWPP

end NFChoice.Foundation.NFStandard
