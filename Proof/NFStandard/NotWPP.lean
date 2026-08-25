import NFStandard.Equivalence
import NFStandard.NotWPPLiteralReplay

namespace NFChoice.Foundation.NFStandard

open scoped Fol
open NFChoice.Foundation.ExactLiteralTrial

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
#print axioms hailperin_proves_not_WPP
#print axioms NF_proves_not_WPP

end NFChoice.Foundation.NFStandard
