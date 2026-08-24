import NominalDfClabStructuralDev005

namespace NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001

open NFChoice.Foundation
open NFChoice.SemanticCore

/-!
One canonical import surface for the only three Metamath definition labels
that do not reduce to reflexivity after deep source expansion.
-/

noncomputable def dfClabStructural (x y : Var) (p : Wff) :
    NPrf
      (NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClabGoal
        x y p) :=
  NFChoice.DirectNominalPrf.Nominal.DfClabStructuralDev005.dfClabStructural
    x y p

noncomputable def dfCleqOfDV (x y z : Var) (A B : Class)
    (hAxExt : NPrf (.imp
      (.all x (Wff.biimp (.classMem (.cv x) (.cv y))
        (.classMem (.cv x) (.cv z))))
      (.classEq (.cv y) (.cv z))))
    (hxA : x ∉ A.fv) (hxB : x ∉ B.fv) :
    NPrf
      (NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfCleqGoal
        x A B) :=
  NFChoice.DirectNominalPrf.Nominal.DefinitionLeafAdapterDev014.dfCleqOfDV
    x y z A B hAxExt hxA hxB

noncomputable def dfClelOfDV (x : Var) (A B : Class)
    (hxA : x ∉ A.fv) (hxB : x ∉ B.fv) :
    NPrf
      (NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClelGoal
        x A B) :=
  NFChoice.DirectNominalPrf.Nominal.DefinitionLeafAdapterDev014.dfClelOfDV
    x A B hxA hxB

#print axioms dfClabStructural
#print axioms dfCleqOfDV
#print axioms dfClelOfDV

end NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001
