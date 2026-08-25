import WPPCompactSourceSyntax
import CompactSyntaxFVDisable

namespace NFChoice.Compiler.WPPCompactSyntaxFVExplicit

open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-! Explicit-only FV equations for the WPP extension; no global simp attributes. -/

theorem fv_syn_wiso (H : Class) (R : Class) (S : Class) (A : Class) (B : Class) :
    (syn_wiso H R S A B).fv = (A.fv) ∪ (B.fv) ∪ (H.fv) ∪ (R.fv) ∪ (S.fv) := by
  have fresh_x : freshVar (H.fv ∪ R.fv ∪ S.fv ∪ A.fv ∪ B.fv) 0 ∉ (H.fv ∪ R.fv ∪ S.fv ∪ A.fv ∪ B.fv) :=
    freshVar_not_mem (H.fv ∪ R.fv ∪ S.fv ∪ A.fv ∪ B.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_x
  have fresh_y : freshVar (H.fv ∪ R.fv ∪ S.fv ∪ A.fv ∪ B.fv) 1 ∉ (H.fv ∪ R.fv ∪ S.fv ∪ A.fv ∪ B.fv) :=
    freshVar_not_mem (H.fv ∪ R.fv ∪ S.fv ∪ A.fv ∪ B.fv) 1
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  have distinct_x_y : freshVar (H.fv ∪ R.fv ∪ S.fv ∪ A.fv ∪ B.fv) 0 ≠ freshVar (H.fv ∪ R.fv ∪ S.fv ∪ A.fv ∪ B.fv) 1 :=
    freshVar_injective (H.fv ∪ R.fv ∪ S.fv ∪ A.fv ∪ B.fv) (by decide)
  ext u
  simp [syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cpprod (A : Class) (B : Class) :
    (syn_cpprod A B).fv = (A.fv) ∪ (B.fv) := by
  ext u
  simp [syn_cpprod, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_ccross  :
    (syn_ccross ).fv = (∅ : Finset Var) := by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_x
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_ccross, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

end NFChoice.Compiler.WPPCompactSyntaxFVExplicit
