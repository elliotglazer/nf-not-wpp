import AlphaTransportFV
import ReplaySupport.Basic

namespace NFChoice.DefinitionLeaves.AlphaFocusedSupport

open NFChoice.Foundation
open NFChoice.ReplaySupport
open NFChoice.SemanticCore
open NFChoice.DefinitionLeaves.AlphaTransport

/-!
Small proof combinators for expectation-guided alpha certificates.  They keep
generated wrappers from repeating dependent equality transport and Finset
membership plumbing at every opaque formal subtree.
-/

/-- Every free variable has a reflexive alpha certificate in the empty binder environment. -/
theorem reflOn_nil (support : Finset Var) : ReflOn [] support := by
  intro u hu
  exact AlphaVar.free (by simp) (by simp)

/-- Add a genuinely renamed binder pair when neither endpoint occurs in the support. -/
theorem ReflOn.cons_of_not_mem {env : BinderEnv} {support : Finset Var}
    {left right : Var} (hleft : left ∉ support) (hright : right ∉ support)
    (tail : ReflOn env support) : ReflOn ((left, right) :: env) support := by
  intro u hu
  exact AlphaVar.there
    (fun h => hleft (h ▸ hu))
    (fun h => hright (h ▸ hu))
    (tail hu)

/-- Freshness descends along an explicitly supplied support inclusion. -/
theorem freshVar_not_mem_of_subset {small large : Finset Var} (offset : Nat)
    (hsub : small ⊆ large) : freshVar large offset ∉ small := by
  intro hmem
  exact freshVar_not_mem large offset (hsub hmem)

/-- Insert a known subset beneath an erasure whose binder is absent from it. -/
theorem subset_erase_of_subset_of_not_mem {small large : Finset Var} {binder : Var}
    (hsub : small ⊆ large) (hnot : binder ∉ small) : small ⊆ large.erase binder := by
  intro u hu
  exact Finset.mem_erase.mpr ⟨fun h => hnot (h ▸ hu), hsub hu⟩

#print axioms reflOn_nil
#print axioms ReflOn.cons_of_not_mem
#print axioms freshVar_not_mem_of_subset
#print axioms subset_erase_of_subset_of_not_mem

end NFChoice.DefinitionLeaves.AlphaFocusedSupport
