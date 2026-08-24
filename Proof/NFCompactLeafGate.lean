import CompactSourceSyntax
import CompactSyntaxFVExplicit
import NFLeafWrappers.Basic
import CompactSyntaxFVDisable

namespace NFChoice.Compiler.NFCompactLeafGate

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.SemanticCore.PartialLowering
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit

theorem axNinCompact {S : Fol.Structure LNF}
    (hNF : Fol.all_realize_sentence S LiteralHailperinNF)
    (x y z w : Var)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    Wff.Valid S
      (syn_wex z (.all w
        (syn_wb (.objMem w z) (syn_wnan (.objMem w x) (.objMem w y))))) := by
  apply NFChoice.NFLeafWrappers.source_ax_nin hNF x y z w
    hxy hxz hxw hyz hyw hzw
    (syn_wex z (.all w
      (syn_wb (.objMem w z) (syn_wnan (.objMem w x) (.objMem w y)))))
  · intro a ha
    simp only [fv_syn_wex, fv_syn_wb, fv_syn_wnan,
      Wff.fv, Class.fv, Finset.mem_erase, Finset.mem_union,
      Finset.mem_singleton] at ha
    simp_all <;> aesop
  · simp [syn_wex, syn_wb, syn_wnan, syn_wa,
      closeNames, lowerClosed, lowerWff?, bindRho?, liftRho?, emptyRho,
      Function.update, hxy, hxz, hxw, hyz, hyw, hzw,
      Wff.ex, Wff.biimp, Wff.conj, Wff.neg,
      Formula.ex, Formula.biimp, Formula.conj, Formula.neg,
      Formula.isSomeSingleton, Formula.singleton, literalAxNin]

theorem axSnCompact {S : Fol.Structure LNF}
    (hNF : Fol.all_realize_sentence S LiteralHailperinNF)
    (x y z : Var)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Wff.Valid S
      (syn_wex y (.all z (syn_wb (.objMem z y) (.objEq z x)))) := by
  apply NFChoice.NFLeafWrappers.source_ax_sn hNF x y z hxy hxz hyz
    (syn_wex y (.all z (syn_wb (.objMem z y) (.objEq z x))))
  · intro a ha
    simp only [fv_syn_wex, fv_syn_wb, Wff.fv, Class.fv,
      Finset.mem_erase, Finset.mem_union, Finset.mem_singleton] at ha
    simp_all <;> aesop
  · simp [syn_wex, syn_wb,
      closeNames, lowerClosed, lowerWff?, bindRho?, liftRho?, emptyRho,
      Function.update, hxy, hxz, hyz,
      Wff.ex, Wff.biimp, Wff.conj, Wff.neg,
      Formula.ex, Formula.biimp, Formula.conj, Formula.neg,
      Formula.isSomeSingleton, Formula.singleton, literalAxSn]

theorem ax1cCompact {S : Fol.Structure LNF}
    (hNF : Fol.all_realize_sentence S LiteralHailperinNF)
    (x y z w : Var)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    Wff.Valid S
      (syn_wex x (.all y
        (syn_wb (.objMem y x)
          (syn_wex z (.all w (syn_wb (.objMem w y) (.objEq w z))))))) := by
  apply NFChoice.NFLeafWrappers.source_ax_1c hNF x y z w
    hxy hxz hxw hyz hyw hzw
    (syn_wex x (.all y
      (syn_wb (.objMem y x)
        (syn_wex z (.all w (syn_wb (.objMem w y) (.objEq w z)))))))
  · intro a ha
    simp only [fv_syn_wex, fv_syn_wb, Wff.fv, Class.fv,
      Finset.mem_erase, Finset.mem_union, Finset.mem_singleton] at ha
    simp_all <;> aesop
  · simp [syn_wex, syn_wb,
      closeNames, lowerClosed, lowerWff?, bindRho?, liftRho?, emptyRho,
      Function.update, hxy, hxz, hxw, hyz, hyw, hzw,
      Wff.ex, Wff.biimp, Wff.conj, Wff.neg,
      Formula.ex, Formula.biimp, Formula.conj, Formula.neg,
      Formula.isSomeSingleton, Formula.singleton, literalAx1c]

#print axioms axNinCompact
#print axioms axSnCompact
#print axioms ax1cCompact

end NFChoice.Compiler.NFCompactLeafGate
