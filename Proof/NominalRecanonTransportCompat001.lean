import NominalRecanonTransportDev

namespace NFChoice.DirectNominalPrf.Nominal.RecanonTransportDev.TRecanonWff

open NFChoice.SemanticCore

/-!
`Wff.neg` is defined as implication into falsum.  The original
type-valued recanonicalization relation exposes the primitive implication
constructor but omitted this derived convenience constructor, even though
the checked certificate emitter uses the corresponding `Prop`-valued helper.
-/

def neg {p q : Wff} (h : TRecanonWff p q) :
    TRecanonWff (Wff.neg p) (Wff.neg q) := by
  unfold Wff.neg
  exact .imp h (.same _)

#print axioms neg

end NFChoice.DirectNominalPrf.Nominal.RecanonTransportDev.TRecanonWff
