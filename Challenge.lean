import NFNotWPP.Surface

/-!
# Standard NF derives the negation of WPP

This is the statement-and-hole surface for the Palomar challenge. WPP means the
**Weak Partition Principle**, not the well-ordering principle. In the exact
source formulation, WPP says that for all sets `x` and `y`, if a function
maps `y` onto `x` and a one-to-one function maps `y` into `x`, then a
one-to-one function maps `x` into `y`.

The final theorem says that this sentence's negation has a formal derivation
from standard NF: extensionality plus the full schema of stratified
comprehension. All transparent syntax, theory, and target declarations are in
the proof-free `NFNotWPP.Surface` module shared verbatim with Solution. The
sole deliberate proof hole is the final theorem below.
-/

namespace NFNotWPP

open scoped NFNotWPP

/-!
PALOMAR CHALLENGE: replace `sorry` by a term. No new axiom should be declared.
The expected solution replaces every use of a finite-basis axiom by its
derivation from standard NF, then structurally quotes the resulting first-order
derivation into this calculus.
-/
theorem NF_proves_not_WPP :
    NF ⊢ₛ' Formula.neg SourceWPPFOL := by
  sorry

end NFNotWPP
