import NominalOneFreeCompletenessBridgeDev003
import NFCompactLeafFinalGate
import CompactSyntaxFVExplicit

namespace NFChoice.DirectNominalPrf.Nominal.NFLiteralXpViaCompletenessDev003

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.DirectNominalPrf.Nominal
open NFChoice.DirectNominalPrf.Nominal.NFLiteralHandlers
open NFChoice.DirectNominalPrf.Nominal.OneFreeCompletenessBridgeDev003

theorem axXpFv (x y z w t : Var)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hxt : x ≠ t)
    (hyz : y ≠ z) (hyw : y ≠ w) (hyt : y ≠ t)
    (hzw : z ≠ w) (hzt : z ≠ t) (hwt : w ≠ t) :
    (axXpGoal x y z w t).fv ⊆ ({x} : Finset Var) := by
  intro a ha
  simp only [axXpGoal, fv_syn_wex, fv_syn_wb, fv_syn_wa, fv_syn_copk,
    Wff.fv, Class.fv, Finset.mem_erase, Finset.mem_union,
    Finset.mem_singleton] at ha ⊢
  simp_all <;> aesop

noncomputable def axXp (x y z w t : Var)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hxt : x ≠ t)
    (hyz : y ≠ z) (hyw : y ≠ w) (hyt : y ≠ t)
    (hzw : z ≠ w) (hzt : z ≠ t) (hwt : w ≠ t) :
    NPrf (axXpGoal x y z w t) :=
  oneFreeNPrfOfValidity x (axXpGoal x y z w t)
    (axXpFv x y z w t hxy hxz hxw hxt hyz hyw hyt hzw hzt hwt)
    (by
      intro S _ hNF
      simpa [axXpGoal] using
        (NFChoice.Compiler.NFCompactLeafFinalGate.axXpCompact
          hNF x y z w t hxy hxz hxw hxt hyz hyw hyt hzw hzt hwt))

#print axioms axXpFv
#print axioms axXp

end NFChoice.DirectNominalPrf.Nominal.NFLiteralXpViaCompletenessDev003
