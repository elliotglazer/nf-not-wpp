import NFStandard.ToHailperin
import NFStandard.TheoryEquivalence

namespace NFChoice.Foundation.NFStandard

open scoped Fol
open NFChoice.Foundation.ExactLiteralTrial

/-!
This is the syntactic closure of `nf_models_literalHailperin`.  The preceding
module proves the finite mathematical content; first-order soundness and
completeness transport its consequences into Flypitch derivations.
-/

/-- Every consequence of the literal Hailperin theory is a consequence of NF. -/
theorem nf_derives_of_literalHailperin_derives {f : Fol.sentence LNF}
    (hf : LiteralHailperinNF ⊢ₛ' f) : NF ⊢ₛ' f :=
  consequence_of_model_inclusion
    (fun _ hNF => nf_models_literalHailperin hNF) hf

/-- In particular, NF formally derives each of Hailperin's eleven axioms. -/
theorem literalAxiom_derivable_in_NF (name : HailperinAxiomName) :
    NF ⊢ₛ' literalAxiomFormula name :=
  nf_derives_of_literalHailperin_derives
    (Fol.saxm' (literalAxiom_mem name))

/-- The exact consequence-transport form used for the final `not WPP` theorem. -/
theorem nf_derives_not_WPP_of_literalHailperin
    (WPP : Fol.sentence LNF)
    (hWPP : LiteralHailperinNF ⊢ₛ' Fol.bd_not WPP) :
    NF ⊢ₛ' Fol.bd_not WPP :=
  nf_derives_of_literalHailperin_derives hWPP

#print axioms nf_derives_of_literalHailperin_derives
#print axioms literalAxiom_derivable_in_NF
#print axioms nf_derives_not_WPP_of_literalHailperin

end NFChoice.Foundation.NFStandard
