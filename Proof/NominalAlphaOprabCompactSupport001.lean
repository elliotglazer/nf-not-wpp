import NominalAlphaTransport

set_option maxRecDepth 30000

namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.DirectNominalPrf.Nominal

/-! A closed structural reflexivity certificate for the three self-paired
binders and one genuinely renamed binder used by `df-oprab`. -/

def nb049_reflOn_self3_fresh
    (x : Var) (y : Var) (z : Var) (a : Var) (w : Var)
    (support : Finset Var) (ha : a ∉ support) (hw : w ∉ support) :
    TReflOn [(z, z), (y, y), (x, x), (a, w)] support := by
  apply TEnvFresh.reflOn
  intro u v huv huv_ne
  simp only [List.mem_cons, List.not_mem_nil, or_false] at huv
  rcases huv with huv | huv | huv | huv
  · cases huv
    exact (huv_ne rfl).elim
  · cases huv
    exact (huv_ne rfl).elim
  · cases huv
    exact (huv_ne rfl).elim
  · cases huv
    exact ⟨ha, hw⟩

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
