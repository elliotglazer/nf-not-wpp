import NFStandard.CylinderToNF
import NFStandard.HailperinAlgebra
import NFStandard.HailperinPresentationBridge
import NFStandard.ToHailperin

namespace NFChoice.Foundation.NFStandard

open scoped Fol
open NFChoice.Foundation.ExactLiteralTrial

/-!
The two directions are deliberately exposed at the model boundary.  The
forward direction verifies Hailperin's eleven finite axioms by ordinary
stratified comprehension.  The reverse direction instantiates the uniform
cylinder compiler with the operations constructed from those eleven axioms.
First-order completeness then converts equality of model classes into full
deductive equivalence.
-/

/-- The exact literal Hailperin basis supplies every stratified comprehension. -/
theorem literalHailperin_models_NF {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) :
    Fol.all_realize_sentence S NF :=
  models_NF_of_cylinder (hailperinCylinderAlgebra hH)
    (hH (literalAxiom_mem .axExt))

/-- Standard NF and the exact literal finite basis have the same models. -/
theorem models_NF_iff_literalHailperinNF (S : Fol.Structure LNF) :
    Fol.all_realize_sentence S NF ↔
      Fol.all_realize_sentence S LiteralHailperinNF :=
  ⟨nf_models_literalHailperin, literalHailperin_models_NF⟩

/-- Standard NF and the exact literal finite basis have the same consequences. -/
theorem nf_literalHailperin_deductivelyEquivalent :
    DeductivelyEquivalent NF LiteralHailperinNF :=
  deductivelyEquivalent_of_models_iff models_NF_iff_literalHailperinNF

/-- The existing finite theory `HailperinNF` supplies standard NF. -/
theorem hailperin_models_NF {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S HailperinNF) :
    Fol.all_realize_sentence S NF :=
  literalHailperin_models_NF (foundationModel_to_literalModel hH)

/-- Standard NF supplies the existing finite theory `HailperinNF`. -/
theorem nf_models_HailperinNF {S : Fol.Structure LNF}
    (hNF : Fol.all_realize_sentence S NF) :
    Fol.all_realize_sentence S HailperinNF :=
  literalModel_to_foundationModel (nf_models_literalHailperin hNF)

/-- Standard `NF` and finite `HailperinNF` have exactly the same models. -/
theorem models_NF_iff_HailperinNF (S : Fol.Structure LNF) :
    Fol.all_realize_sentence S NF ↔
      Fol.all_realize_sentence S HailperinNF :=
  ⟨nf_models_HailperinNF, hailperin_models_NF⟩

/--
Full equivalence of the standard stratified-comprehension theory and
Hailperin's finite first-order presentation.
-/
theorem nf_hailperin_deductivelyEquivalent :
    DeductivelyEquivalent NF HailperinNF :=
  deductivelyEquivalent_of_models_iff models_NF_iff_HailperinNF

#print axioms literalHailperin_models_NF
#print axioms models_NF_iff_HailperinNF
#print axioms nf_hailperin_deductivelyEquivalent

end NFChoice.Foundation.NFStandard
