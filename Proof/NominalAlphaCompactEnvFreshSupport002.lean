import NominalAlphaTransport

set_option maxRecDepth 30000

namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open NFChoice.DirectNominalPrf.Nominal

/-! Type-explicit successor to the compact `TEnvFresh` constructors.

`NFChoice.Foundation.Var` and `NFChoice.SemanticCore.Var` are distinct names
in this import context.  Every occurrence below is therefore qualified with
the exact variable type used by `TBinderEnv` and `TEnvFresh`. -/

namespace TEnvFresh

def nil (support : Finset NFChoice.SemanticCore.Var) :
    TEnvFresh [] support := by
  intro x y hmem hne
  simp only [List.not_mem_nil] at hmem

def consSame
    {env : TBinderEnv}
    {support : Finset NFChoice.SemanticCore.Var}
    (x : NFChoice.SemanticCore.Var) (tail : TEnvFresh env support) :
    TEnvFresh ((x, x) :: env) support := by
  intro a b hmem hne
  simp only [List.mem_cons] at hmem
  rcases hmem with hmem | hmem
  · cases hmem
    exact (hne rfl).elim
  · exact tail hmem hne

def consFresh
    {env : TBinderEnv}
    {support : Finset NFChoice.SemanticCore.Var}
    (x : NFChoice.SemanticCore.Var) (y : NFChoice.SemanticCore.Var)
    (hx : x ∉ support) (hy : y ∉ support)
    (tail : TEnvFresh env support) :
    TEnvFresh ((x, y) :: env) support := by
  intro a b hmem hne
  simp only [List.mem_cons] at hmem
  rcases hmem with hmem | hmem
  · cases hmem
    exact ⟨hx, hy⟩
  · exact tail hmem hne

end TEnvFresh

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
