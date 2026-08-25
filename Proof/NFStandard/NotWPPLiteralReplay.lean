import NFStandard.WPP
import NominalWPPReplayChunk018Compact001
import ReplaySupport.Basic
import WPPCompactSyntaxFVExplicit

namespace NFChoice.Foundation.NFStandard

open scoped Fol
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal.BoundedNominalLoweringBridgeDev004

/- Soundness of the accepted nominal replay, stated at its source WPP. -/
set_option maxRecDepth 30000 in
theorem literalHailperin_valid_not_WPP {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) :
    Wff.Valid S (.neg syn_wwpp) := by
  intro v
  let a : S := v 0
  let rho : Var → Fin 1 := fun _ => 0
  let xs : DVec S 1 := DVec.cons a DVec.nil
  let v0 : Var → S := fun _ => a
  have hprf : Fol.prf LiteralHailperinNF.fst
      (Nominal.lowerWff (finValRho rho) (.neg syn_wwpp)) :=
    NFChoice.DirectNominalPrf.WPPReplay.g_wppfiniteblocknotwppndv
      (finValRho rho)
  have hs : Fol.realize_formula v0
      (Nominal.lowerWff (finValRho rho) (.neg syn_wwpp)) DVec.nil := by
    apply Fol.formula_soundness hprf S v0
    intro f hf
    rcases hf with ⟨g, hg, rfl⟩
    exact (Fol.realize_sentence_iff v0 g).mp (hH hg)
  rw [lowerWff_toFlypitch rho (.neg syn_wwpp)] at hs
  have hv : ∀ k (hk : k < 1), xs.nth k hk = v0 k := by
    intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
    subst k
    simp [xs, v0, a]
  have hb : Fol.realize_bounded_formula xs
      (Formula.toFlypitch (Lowering.lowerWff rho (.neg syn_wwpp)))
      DVec.nil :=
    (Fol.realize_bounded_formula_iff hv _ DVec.nil).2 hs
  have hconst : Wff.Holds S v0 (.neg syn_wwpp) :=
    (Lowering.lowerWff_realize_iff rho xs v0
      (by intro x; simp [rho, xs, v0, a]) (.neg syn_wwpp)).2 hb
  have hagree : AgreesOn (Wff.neg syn_wwpp).fv v0 v := by
    intro x hx
    simp [Wff.neg, Wff.fv, fv_syn_wwpp] at hx
  exact (Wff.holds_congr_fv (.neg syn_wwpp) v0 v hagree).mp hconst

/-- The accepted replay proves the exact lowered WPP sentence from the literal basis. -/
theorem literalHailperin_proves_not_WPP :
    LiteralHailperinNF ⊢ₛ' Fol.bd_not WPP := by
  unfold WPP
  exact NFChoice.ReplaySupport.derives_not_of_nominal_validity
    syn_wwpp WPPSyntax fv_syn_wwpp lowerClosed_syn_wwpp
    (fun _ _ hH => literalHailperin_valid_not_WPP hH)

end NFChoice.Foundation.NFStandard
