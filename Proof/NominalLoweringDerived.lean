import NominalLoweringLemmas

namespace NFChoice.DirectNominalPrf.Nominal

open NFChoice.SemanticCore

/-!
Logical wrappers whose Metamath freshness condition follows directly from
the nominal free-variable computation.  Keeping them separate from the
generic lowering theorem makes the source emitter's primitive table small
and explicit.
-/

/-- Metamath `ax-6`: `x` is not free in `¬ ∀ x, p`. -/
def ax6 (x : Var) (p : Wff) :
    NPrf (.imp (Wff.neg (.all x p))
      (.all x (Wff.neg (.all x p)))) :=
  ax17 (Wff.neg (.all x p)) x (by
    simp [Wff.neg, Wff.fv])

#print axioms ax6

end NFChoice.DirectNominalPrf.Nominal
