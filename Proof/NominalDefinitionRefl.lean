import NominalRecanonTransportDev

namespace NFChoice.DirectNominalPrf.Nominal

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.DirectCertificate.ClassBoundaryCoreDev006

/-! Proof-object reflexivity for class-valued definitional leaves. -/

noncomputable def classEqRefl (A : Class) :
    NPrf (.classEq A A) :=
  fun rho => by
    simp only [lowerWff]
    exact Fol.prf.allI (Fol.biimp_refl _ _)

#print axioms classEqRefl

end NFChoice.DirectNominalPrf.Nominal
