import WPPCompactSyntaxFVExplicitPart005

namespace NFChoice.Compiler.WPPCompactSyntaxFVExplicit

open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-! Explicit-only FV equations for the WPP extension; no global simp attributes. -/

theorem fv_syn_chnwcutmap (R : Class) (D : Class) :
    (syn_chnwcutmap R D).fv = (D.fv) ∪ (R.fv) := by
  have fresh_p : freshVar (R.fv ∪ D.fv) 0 ∉ (R.fv ∪ D.fv) :=
    freshVar_not_mem (R.fv ∪ D.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_p
  ext u
  simp [syn_chnwcutmap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chnqmap1 (A : Class) :
    (syn_chnqmap1 A).fv = A.fv := by
  ext u
  simp [syn_chnqmap1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_clntp  :
    (syn_clntp ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_clntp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_clntpc (A : Class) :
    (syn_clntpc A).fv = A.fv := by
  ext u
  simp [syn_clntpc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwrels, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clntp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_clnker (R : Class) :
    (syn_clnker R).fv = R.fv := by
  ext u
  simp [syn_clnker, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_clnquo (R : Class) (A : Class) :
    (syn_clnquo R A).fv = (A.fv) ∪ (R.fv) := by
  ext u
  simp [syn_clnquo, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cqs, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwpphit (F : Class) (I : Class) (C : Class) :
    (syn_cwpphit F I C).fv = (C.fv) ∪ (F.fv) ∪ (I.fv) := by
  ext u
  simp [syn_cwpphit, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chnwsegfn (R : Class) (D : Class) :
    (syn_chnwsegfn R D).fv = (D.fv) ∪ (R.fv) := by
  ext u
  simp [syn_chnwsegfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chnwcodefn (R : Class) :
    (syn_chnwcodefn R).fv = R.fv := by
  ext u
  simp [syn_chnwcodefn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chnwcutfn (R : Class) (D : Class) :
    (syn_chnwcutfn R D).fv = (D.fv) ∪ (R.fv) := by
  ext u
  simp [syn_chnwcutfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcodefn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwsegfn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chnwcutrel (R : Class) (D : Class) :
    (syn_chnwcutrel R D).fv = (D.fv) ∪ (R.fv) := by
  ext u
  simp [syn_chnwcutrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_clnqrel (R : Class) :
    (syn_clnqrel R).fv = R.fv := by
  have fresh_a : freshVar (R.fv) 0 ∉ (R.fv) :=
    freshVar_not_mem (R.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_a
  have fresh_b : freshVar (R.fv) 1 ∉ (R.fv) :=
    freshVar_not_mem (R.fv) 1
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_b
  have fresh_x : freshVar (R.fv) 2 ∉ (R.fv) :=
    freshVar_not_mem (R.fv) 2
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_x
  have fresh_y : freshVar (R.fv) 3 ∉ (R.fv) :=
    freshVar_not_mem (R.fv) 3
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  have distinct_a_b : freshVar (R.fv) 0 ≠ freshVar (R.fv) 1 :=
    freshVar_injective (R.fv) (by decide)
  have distinct_a_x : freshVar (R.fv) 0 ≠ freshVar (R.fv) 2 :=
    freshVar_injective (R.fv) (by decide)
  have distinct_a_y : freshVar (R.fv) 0 ≠ freshVar (R.fv) 3 :=
    freshVar_injective (R.fv) (by decide)
  have distinct_b_x : freshVar (R.fv) 1 ≠ freshVar (R.fv) 2 :=
    freshVar_injective (R.fv) (by decide)
  have distinct_b_y : freshVar (R.fv) 1 ≠ freshVar (R.fv) 3 :=
    freshVar_injective (R.fv) (by decide)
  have distinct_x_y : freshVar (R.fv) 2 ≠ freshVar (R.fv) 3 :=
    freshVar_injective (R.fv) (by decide)
  ext u
  simp [syn_clnqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_clnqord (R : Class) (C : Class) :
    (syn_clnqord R C).fv = (C.fv) ∪ (R.fv) := by
  ext u
  simp [syn_clnqord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_clnpwc (A : Class) :
    (syn_clnpwc A).fv = A.fv := by
  have fresh_d : freshVar (A.fv) 0 ∉ (A.fv) :=
    freshVar_not_mem (A.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_d
  have fresh_r : freshVar (A.fv) 1 ∉ (A.fv) :=
    freshVar_not_mem (A.fv) 1
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_r
  have distinct_d_r : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [syn_clnpwc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfound, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clntpc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfrecteq (F : Class) (G : Class) (I : Class) :
    (syn_cfrecteq F G I).fv = (F.fv) ∪ (G.fv) ∪ (I.fv) := by
  ext u
  simp [syn_cfrecteq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfix, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctcfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni1, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chnqinc (D : Class) (A : Class) :
    (syn_chnqinc D A).fv = (A.fv) ∪ (D.fv) := by
  ext u
  simp [syn_chnqinc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_clndifop  :
    (syn_clndifop ).fv = (∅ : Finset Var) := by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_x
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_clndifop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_clnpwasymfn  :
    (syn_clnpwasymfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_clnpwasymfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clndifop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfdord (R : Class) (A : Class) (B : Class) :
    (syn_cfdord R A B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) := by
  ext u
  simp [syn_cfdord, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

end NFChoice.Compiler.WPPCompactSyntaxFVExplicit
