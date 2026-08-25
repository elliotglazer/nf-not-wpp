import WPPCompactSyntaxFVExplicitPart002

namespace NFChoice.Compiler.WPPCompactSyntaxFVExplicit

open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-! Explicit-only FV equations for the WPP extension; no global simp attributes. -/

theorem fv_syn_cfrec (F : Class) (I : Class) :
    (syn_cfrec F I).fv = (F.fv) ∪ (I.fv) := by
  have fresh_x : freshVar (F.fv ∪ I.fv) 0 ∉ (F.fv ∪ I.fv) :=
    freshVar_not_mem (F.fv ∪ I.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_x
  ext u
  simp [syn_cfrec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cclos1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_wwpp  :
    (syn_wwpp ).fv = (∅ : Finset Var) := by
  have fresh_f : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_f
  have fresh_g : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_g
  have fresh_h : freshVar ((∅ : Finset Var)) 2 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 2
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_h
  have fresh_x : freshVar ((∅ : Finset Var)) 3 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 3
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_x
  have fresh_y : freshVar ((∅ : Finset Var)) 4 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 4
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  have distinct_f_g : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_f_h : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_f_x : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_f_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 4 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_g_h : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_g_x : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_g_y : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 4 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_h_x : freshVar ((∅ : Finset Var)) 2 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_h_y : freshVar ((∅ : Finset Var)) 2 ≠ freshVar ((∅ : Finset Var)) 4 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_x_y : freshVar ((∅ : Finset Var)) 3 ≠ freshVar ((∅ : Finset Var)) 4 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_wwpp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cqkrel (A : Class) :
    (syn_cqkrel A).fv = A.fv := by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) :=
    freshVar_not_mem (A.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_x
  have fresh_y : freshVar (A.fv) 1 ∉ (A.fv) :=
    freshVar_not_mem (A.fv) 1
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  have fresh_z : freshVar (A.fv) 2 ∉ (A.fv) :=
    freshVar_not_mem (A.fv) 2
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_z
  have distinct_x_y : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_x_z : freshVar (A.fv) 0 ≠ freshVar (A.fv) 2 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_y_z : freshVar (A.fv) 1 ≠ freshVar (A.fv) 2 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [syn_cqkrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

end NFChoice.Compiler.WPPCompactSyntaxFVExplicit
