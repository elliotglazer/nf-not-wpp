import NominalOneFreeCompletenessBridgeDev003
import NFCompactLeafFinalGate
import CompactSyntaxFVExplicit

namespace NFChoice.DirectNominalPrf.Nominal.NFLiteralRemainingViaCompletenessDev001

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.DirectNominalPrf.Nominal
open NFChoice.DirectNominalPrf.Nominal.NFLiteralHandlers
open NFChoice.DirectNominalPrf.Nominal.OneFreeCompletenessBridgeDev003

macro "solve_fv" : tactic =>
  `(tactic|
    first
    | (intro a ha
       simp only [fv_syn_wex, fv_syn_wb, fv_syn_wa, fv_syn_copk,
         fv_syn_csn, Wff.fv, Class.fv, Finset.mem_erase,
         Finset.mem_union, Finset.mem_singleton] at ha ⊢
       simp_all <;> aesop)
    | (simp only [fv_syn_wex, fv_syn_wb, fv_syn_wa, fv_syn_copk,
         fv_syn_csn, Wff.fv, Class.fv, Finset.mem_erase,
         Finset.mem_union, Finset.mem_singleton]
       aesop))

theorem axCnvFv (x y z w : Var)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    (axCnvGoal x y z w).fv ⊆ ({x} : Finset Var) := by
  simp only [axCnvGoal]
  solve_fv

noncomputable def axCnv (x y z w : Var)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    NPrf (axCnvGoal x y z w) :=
  oneFreeNPrfOfValidity x (axCnvGoal x y z w)
    (axCnvFv x y z w hxy hxz hxw hyz hyw hzw)
    (by
      intro S _ hNF
      simpa [axCnvGoal] using
        (NFChoice.Compiler.NFCompactLeafFinalGate.axCnvCompact
          hNF x y z w hxy hxz hxw hyz hyw hzw))

theorem axSsetFv (x y z w : Var)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    (axSsetGoal x y z w).fv ⊆ ({x} : Finset Var) := by
  simp only [axSsetGoal]
  solve_fv

noncomputable def axSset (x y z w : Var)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    NPrf (axSsetGoal x y z w) :=
  oneFreeNPrfOfValidity x (axSsetGoal x y z w)
    (axSsetFv x y z w hxy hxz hxw hyz hyw hzw)
    (by
      intro S _ hNF
      simpa [axSsetGoal] using
        (NFChoice.Compiler.NFCompactLeafFinalGate.axSsetCompact
          hNF x y z w hxy hxz hxw hyz hyw hzw))

theorem axSiFv (x y z w : Var)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    (axSiGoal x y z w).fv ⊆ ({x} : Finset Var) := by
  simp only [axSiGoal]
  solve_fv

noncomputable def axSi (x y z w : Var)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    NPrf (axSiGoal x y z w) :=
  oneFreeNPrfOfValidity x (axSiGoal x y z w)
    (axSiFv x y z w hxy hxz hxw hyz hyw hzw)
    (by
      intro S _ hNF
      simpa [axSiGoal] using
        (NFChoice.Compiler.NFCompactLeafFinalGate.axSiCompact
          hNF x y z w hxy hxz hxw hyz hyw hzw))

theorem axIns2Fv (x y z w t : Var)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hxt : x ≠ t)
    (hyz : y ≠ z) (hyw : y ≠ w) (hyt : y ≠ t)
    (hzw : z ≠ w) (hzt : z ≠ t) (hwt : w ≠ t) :
    (axIns2Goal x y z w t).fv ⊆ ({x} : Finset Var) := by
  simp only [axIns2Goal]
  solve_fv

noncomputable def axIns2 (x y z w t : Var)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hxt : x ≠ t)
    (hyz : y ≠ z) (hyw : y ≠ w) (hyt : y ≠ t)
    (hzw : z ≠ w) (hzt : z ≠ t) (hwt : w ≠ t) :
    NPrf (axIns2Goal x y z w t) :=
  oneFreeNPrfOfValidity x (axIns2Goal x y z w t)
    (axIns2Fv x y z w t hxy hxz hxw hxt hyz hyw hyt hzw hzt hwt)
    (by
      intro S _ hNF
      simpa [axIns2Goal] using
        (NFChoice.Compiler.NFCompactLeafFinalGate.axIns2Compact
          hNF x y z w t hxy hxz hxw hxt hyz hyw hyt hzw hzt hwt))

theorem axIns3Fv (x y z w t : Var)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hxt : x ≠ t)
    (hyz : y ≠ z) (hyw : y ≠ w) (hyt : y ≠ t)
    (hzw : z ≠ w) (hzt : z ≠ t) (hwt : w ≠ t) :
    (axIns3Goal x y z w t).fv ⊆ ({x} : Finset Var) := by
  simp only [axIns3Goal]
  solve_fv

noncomputable def axIns3 (x y z w t : Var)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hxt : x ≠ t)
    (hyz : y ≠ z) (hyw : y ≠ w) (hyt : y ≠ t)
    (hzw : z ≠ w) (hzt : z ≠ t) (hwt : w ≠ t) :
    NPrf (axIns3Goal x y z w t) :=
  oneFreeNPrfOfValidity x (axIns3Goal x y z w t)
    (axIns3Fv x y z w t hxy hxz hxw hxt hyz hyw hyt hzw hzt hwt)
    (by
      intro S _ hNF
      simpa [axIns3Goal] using
        (NFChoice.Compiler.NFCompactLeafFinalGate.axIns3Compact
          hNF x y z w t hxy hxz hxw hxt hyz hyw hyt hzw hzt hwt))

theorem axTypeLowerFv (x y z w : Var)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    (axTypeLowerGoal x y z w).fv ⊆ ({x} : Finset Var) := by
  simp only [axTypeLowerGoal]
  solve_fv

noncomputable def axTypeLower (x y z w : Var)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    NPrf (axTypeLowerGoal x y z w) :=
  oneFreeNPrfOfValidity x (axTypeLowerGoal x y z w)
    (axTypeLowerFv x y z w hxy hxz hxw hyz hyw hzw)
    (by
      intro S _ hNF
      simpa [axTypeLowerGoal] using
        (NFChoice.Compiler.NFCompactLeafFinalGate.axTypeLowerCompact
          hNF x y z w hxy hxz hxw hyz hyw hzw))

#print axioms axCnv
#print axioms axSset
#print axioms axSi
#print axioms axIns2
#print axioms axIns3
#print axioms axTypeLower

end NFChoice.DirectNominalPrf.Nominal.NFLiteralRemainingViaCompletenessDev001
