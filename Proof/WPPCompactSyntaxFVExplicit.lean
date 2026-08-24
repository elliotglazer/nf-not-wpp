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

theorem fv_syn_cdomfn  :
    (syn_cdomfn ).fv = (∅ : Finset Var) := by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_x
  ext u
  simp [syn_cdomfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cranfn  :
    (syn_cranfn ).fv = (∅ : Finset Var) := by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_x
  ext u
  simp [syn_cranfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cmuc  :
    (syn_cmuc ).fv = (∅ : Finset Var) := by
  have fresh_a : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_a
  have fresh_b : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_b
  have fresh_g : freshVar ((∅ : Finset Var)) 2 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 2
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_g
  have fresh_m : freshVar ((∅ : Finset Var)) 3 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 3
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_m
  have fresh_n : freshVar ((∅ : Finset Var)) 4 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 4
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_n
  have distinct_a_b : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_a_g : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_a_m : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_a_n : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 4 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_b_g : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 2 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_b_m : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_b_n : freshVar ((∅ : Finset Var)) 1 ≠ freshVar ((∅ : Finset Var)) 4 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_g_m : freshVar ((∅ : Finset Var)) 2 ≠ freshVar ((∅ : Finset Var)) 3 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_g_n : freshVar ((∅ : Finset Var)) 2 ≠ freshVar ((∅ : Finset Var)) 4 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  have distinct_m_n : freshVar ((∅ : Finset Var)) 3 ≠ freshVar ((∅ : Finset Var)) 4 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_cmuc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

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

theorem fv_syn_cfdmem  :
    (syn_cfdmem ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_cfdmem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfdprj0  :
    (syn_cfdprj0 ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_cfdprj0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfdprj1  :
    (syn_cfdprj1 ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_cfdprj1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfddom (A : Class) (B : Class) :
    (syn_cfddom A B).fv = (A.fv) ∪ (B.fv) := by
  ext u
  simp [syn_cfddom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfde0 (A : Class) (B : Class) :
    (syn_cfde0 A B).fv = (A.fv) ∪ (B.fv) := by
  ext u
  simp [syn_cfde0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfddom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdprj0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfde1 (A : Class) (B : Class) :
    (syn_cfde1 A B).fv = (A.fv) ∪ (B.fv) := by
  ext u
  simp [syn_cfde1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfddom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdprj1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfdsep (A : Class) (B : Class) :
    (syn_cfdsep A B).fv = (A.fv) ∪ (B.fv) := by
  ext u
  simp [syn_cfdsep, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfde0, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfde1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfdlift (R : Class) :
    (syn_cfdlift R).fv = R.fv := by
  ext u
  simp [syn_cfdlift, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cqkrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfdnonmin (R : Class) (A : Class) (B : Class) :
    (syn_cfdnonmin R A B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) := by
  ext u
  simp [syn_cfdnonmin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdlift, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdsep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfdminsep (R : Class) (A : Class) (B : Class) :
    (syn_cfdminsep R A B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) := by
  ext u
  simp [syn_cfdminsep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdnonmin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdsep, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_csep2 (A : Class) (B : Class) :
    (syn_csep2 A B).fv = (A.fv) ∪ (B.fv) := by
  have fresh_z : freshVar (A.fv ∪ B.fv) 0 ∉ (A.fv ∪ B.fv) :=
    freshVar_not_mem (A.fv ∪ B.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_z
  ext u
  simp [syn_csep2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_ckqrel (A : Class) :
    (syn_ckqrel A).fv = A.fv := by
  have fresh_x : freshVar (A.fv) 0 ∉ (A.fv) :=
    freshVar_not_mem (A.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_x
  have fresh_y : freshVar (A.fv) 1 ∉ (A.fv) :=
    freshVar_not_mem (A.fv) 1
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  have distinct_x_y : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfdminvalp (R : Class) (A : Class) (B : Class) (C : Class) :
    (syn_cfdminvalp R A B C).fv = (A.fv) ∪ (B.fv) ∪ (C.fv) ∪ (R.fv) := by
  ext u
  simp [syn_cfdminvalp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminsep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni1, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfdminq (R : Class) (A : Class) (B : Class) :
    (syn_cfdminq R A B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) := by
  ext u
  simp [syn_cfdminq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminsep, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfdpivmap2 (R : Class) (A : Class) (B : Class) :
    (syn_cfdpivmap2 R A B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) := by
  have fresh_p : freshVar (R.fv ∪ A.fv ∪ B.fv) 0 ∉ (R.fv ∪ A.fv ∪ B.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_p
  ext u
  simp [syn_cfdpivmap2, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminvalp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfdpivrange2 (R : Class) (A : Class) (B : Class) :
    (syn_cfdpivrange2 R A B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) := by
  ext u
  simp [syn_cfdpivrange2, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivmap2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfpiv (R : Class) (A : Class) (B : Class) (C : Class) :
    (syn_cfpiv R A B C).fv = (A.fv) ∪ (B.fv) ∪ (C.fv) ∪ (R.fv) := by
  have fresh_b : freshVar (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0 ∉ (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_b
  have fresh_c : freshVar (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 1 ∉ (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 1
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_c
  have distinct_b_c : freshVar (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0 ≠ freshVar (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 1 :=
    freshVar_injective (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) (by decide)
  ext u
  simp [syn_cfpiv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfdif (R : Class) (A : Class) (B : Class) :
    (syn_cfdif R A B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) := by
  have fresh_d : freshVar (R.fv ∪ A.fv ∪ B.fv) 0 ∉ (R.fv ∪ A.fv ∪ B.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_d
  have fresh_x : freshVar (R.fv ∪ A.fv ∪ B.fv) 1 ∉ (R.fv ∪ A.fv ∪ B.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv) 1
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_x
  have fresh_y : freshVar (R.fv ∪ A.fv ∪ B.fv) 2 ∉ (R.fv ∪ A.fv ∪ B.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv) 2
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_y
  have distinct_d_x : freshVar (R.fv ∪ A.fv ∪ B.fv) 0 ≠ freshVar (R.fv ∪ A.fv ∪ B.fv) 1 :=
    freshVar_injective (R.fv ∪ A.fv ∪ B.fv) (by decide)
  have distinct_d_y : freshVar (R.fv ∪ A.fv ∪ B.fv) 0 ≠ freshVar (R.fv ∪ A.fv ∪ B.fv) 2 :=
    freshVar_injective (R.fv ∪ A.fv ∪ B.fv) (by decide)
  have distinct_x_y : freshVar (R.fv ∪ A.fv ∪ B.fv) 1 ≠ freshVar (R.fv ∪ A.fv ∪ B.fv) 2 :=
    freshVar_injective (R.fv ∪ A.fv ∪ B.fv) (by decide)
  ext u
  simp [syn_cfdif, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfpiv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfdrow (R : Class) (A : Class) (B : Class) (C : Class) :
    (syn_cfdrow R A B C).fv = (A.fv) ∪ (B.fv) ∪ (C.fv) ∪ (R.fv) := by
  have fresh_d : freshVar (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0 ∉ (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_d
  ext u
  simp [syn_cfdrow, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfdcode (R : Class) (A : Class) (B : Class) (C : Class) :
    (syn_cfdcode R A B C).fv = (A.fv) ∪ (B.fv) ∪ (C.fv) ∪ (R.fv) := by
  have fresh_q : freshVar (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0 ∉ (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_q
  have fresh_x : freshVar (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 1 ∉ (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 1
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_x
  have distinct_q_x : freshVar (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0 ≠ freshVar (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 1 :=
    freshVar_injective (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) (by decide)
  ext u
  simp [syn_cfdcode, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrow, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfdrowrel (R : Class) (A : Class) (B : Class) :
    (syn_cfdrowrel R A B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) := by
  ext u
  simp [syn_cfdrowrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfdrowfib (R : Class) (A : Class) (B : Class) (C : Class) :
    (syn_cfdrowfib R A B C).fv = (A.fv) ∪ (B.fv) ∪ (C.fv) ∪ (R.fv) := by
  have fresh_d : freshVar (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0 ∉ (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_d
  ext u
  simp [syn_cfdrowfib, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfdcodemap2 (R : Class) (A : Class) (B : Class) (C : Class) :
    (syn_cfdcodemap2 R A B C).fv = (A.fv) ∪ (B.fv) ∪ (C.fv) ∪ (R.fv) := by
  have fresh_u : freshVar (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0 ∉ (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_u
  ext u
  simp [syn_cfdcodemap2, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowfib, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfdpointrel (A : Class) :
    (syn_cfdpointrel A).fv = A.fv := by
  ext u
  simp [syn_cfdpointrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfdglobalrowmap (R : Class) (A : Class) (B : Class) :
    (syn_cfdglobalrowmap R A B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) := by
  have fresh_u : freshVar (R.fv ∪ A.fv ∪ B.fv) 0 ∉ (R.fv ∪ A.fv ∪ B.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_u
  ext u
  simp [syn_cfdglobalrowmap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowfib, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cfdcolcodemap (R : Class) (A : Class) (B : Class) :
    (syn_cfdcolcodemap R A B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) := by
  ext u
  simp [syn_cfdcolcodemap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdglobalrowmap, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpointrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chwcodes (A : Class) :
    (syn_chwcodes A).fv = A.fv := by
  ext u
  simp [syn_chwcodes, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chwiso (A : Class) :
    (syn_chwiso A).fv = A.fv := by
  have fresh_h : freshVar (A.fv) 0 ∉ (A.fv) :=
    freshVar_not_mem (A.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_h
  have fresh_u : freshVar (A.fv) 1 ∉ (A.fv) :=
    freshVar_not_mem (A.fv) 1
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_u
  have fresh_v : freshVar (A.fv) 2 ∉ (A.fv) :=
    freshVar_not_mem (A.fv) 2
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_v
  have distinct_h_u : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_h_v : freshVar (A.fv) 0 ≠ freshVar (A.fv) 2 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_u_v : freshVar (A.fv) 1 ≠ freshVar (A.fv) 2 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [syn_chwiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcodes, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chwrels  :
    (syn_chwrels ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_chwrels, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chwbij  :
    (syn_chwbij ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_chwbij, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfuns, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chwtrn  :
    (syn_chwtrn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_chwtrn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompose, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chwgen  :
    (syn_chwgen ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_chwgen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cdomfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwtrn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cranfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chwcn (A : Class) :
    (syn_chwcn A).fv = A.fv := by
  ext u
  simp [syn_chwcn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcodes, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwrels, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chwniso (A : Class) :
    (syn_chwniso A).fv = A.fv := by
  ext u
  simp [syn_chwniso, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chnord (A : Class) :
    (syn_chnord A).fv = A.fv := by
  ext u
  simp [syn_chnord, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cqs, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chncard (A : Class) :
    (syn_chncard A).fv = A.fv := by
  ext u
  simp [syn_chncard, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chwbases (A : Class) :
    (syn_chwbases A).fv = A.fv := by
  ext u
  simp [syn_chwbases, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chwcards (A : Class) :
    (syn_chwcards A).fv = A.fv := by
  ext u
  simp [syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbases, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cqs, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chnwcutcode (R : Class) (D : Class) (C : Class) :
    (syn_chnwcutcode R D C).fv = (C.fv) ∪ (D.fv) ∪ (R.fv) := by
  ext u
  simp [syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

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

theorem fv_syn_ctcnn  :
    (syn_ctcnn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_ctcnn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctcfn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cpwpull (F : Class) (R : Class) :
    (syn_cpwpull F R).fv = (F.fv) ∪ (R.fv) := by
  ext u
  simp [syn_cpwpull, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_clnpwkerfn  :
    (syn_clnpwkerfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_clnpwkerfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clndifop, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwasymfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_clninterop  :
    (syn_clninterop ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_clninterop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clndifop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_clnimagecrossfn  :
    (syn_clnimagecrossfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_clnimagecrossfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_clnimageresfn  :
    (syn_clnimageresfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_clnimageresfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimagecrossfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clninterop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_clnimageop  :
    (syn_clnimageop ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_clnimageop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageresfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cranfn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_clnpwcnvkerfn  :
    (syn_clnpwcnvkerfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_clnpwcnvkerfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwkerfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_clnpwclasspairfn  :
    (syn_clnpwclasspairfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_clnpwclasspairfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwcnvkerfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_clnpwclassfn  :
    (syn_clnpwclassfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_clnpwclassfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageop, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwclasspairfn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_clnpwpw1secondfn  :
    (syn_clnpwpw1secondfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_clnpwpw1secondfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfullfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_clnpwquoinputfn  :
    (syn_clnpwquoinputfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_clnpwquoinputfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwpw1secondfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_clnpwquofn  :
    (syn_clnpwquofn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_clnpwquofn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwclassfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwquoinputfn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_clnpairraisefn  :
    (syn_clnpairraisefn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_clnpairraisefn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_clnsifn  :
    (syn_clnsifn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_clnsifn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfullfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpairraisefn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_clnpwsirelfn  :
    (syn_clnpwsirelfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_clnpwsirelfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnsifn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwppreach (F : Class) (C : Class) :
    (syn_cwppreach F C).fv = (C.fv) ∪ (F.fv) := by
  ext u
  simp [syn_cwppreach, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwppcand (F : Class) (C : Class) :
    (syn_cwppcand F C).fv = (C.fv) ∪ (F.fv) := by
  ext u
  simp [syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppreach, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwpppredfam (F : Class) (C : Class) :
    (syn_cwpppredfam F C).fv = (C.fv) ∪ (F.fv) := by
  ext u
  simp [syn_cwpppredfam, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctcfn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwpppostcomp (F : Class) :
    (syn_cwpppostcomp F).fv = F.fv := by
  ext u
  simp [syn_cwpppostcomp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompose, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwppupperpreop (C : Class) :
    (syn_cwppupperpreop C).fv = C.fv := by
  ext u
  simp [syn_cwppupperpreop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwpppowlayerseq (F : Class) (C : Class) :
    (syn_cwpppowlayerseq F C).fv = (C.fv) ∪ (F.fv) := by
  ext u
  simp [syn_cwpppowlayerseq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctcfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppostcomp, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppupperpreop, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwpphitfam (F : Class) (C : Class) :
    (syn_cwpphitfam F C).fv = (C.fv) ∪ (F.fv) := by
  ext u
  simp [syn_cwpphitfam, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowlayerseq, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwpppredmemrel (F : Class) (C : Class) :
    (syn_cwpppredmemrel F C).fv = (C.fv) ∪ (F.fv) := by
  ext u
  simp [syn_cwpppredmemrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppredfam, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwpphitmemrel (F : Class) (C : Class) :
    (syn_cwpphitmemrel F C).fv = (C.fv) ∪ (F.fv) := by
  ext u
  simp [syn_cwpphitmemrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphitfam, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwppreachincb (F : Class) (C : Class) :
    (syn_cwppreachincb F C).fv = (C.fv) ∪ (F.fv) := by
  ext u
  simp [syn_cwppreachincb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphitmemrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppredmemrel, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwppimageat (D : Class) :
    (syn_cwppimageat D).fv = D.fv := by
  ext u
  simp [syn_cwppimageat, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwpppowateq (F : Class) (D : Class) :
    (syn_cwpppowateq F D).fv = (D.fv) ∪ (F.fv) := by
  ext u
  simp [syn_cwpppowateq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfix, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctcfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppimageat, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppostcomp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwppprecomp (F : Class) :
    (syn_cwppprecomp F).fv = F.fv := by
  ext u
  simp [syn_cwppprecomp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompose, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwpppowcommeq (F : Class) :
    (syn_cwpppowcommeq F).fv = F.fv := by
  ext u
  simp [syn_cwpppowcommeq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfix, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppostcomp, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppprecomp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwecutiso (R : Class) (D : Class) (S : Class) (E : Class) :
    (syn_cwecutiso R D S E).fv = (D.fv) ∪ (E.fv) ∪ (R.fv) ∪ (S.fv) := by
  have fresh_f : freshVar (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) 0 ∉ (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) :=
    freshVar_not_mem (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_f
  have fresh_u : freshVar (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) 1 ∉ (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) :=
    freshVar_not_mem (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) 1
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_u
  have fresh_x : freshVar (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) 2 ∉ (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) :=
    freshVar_not_mem (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) 2
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_x
  have distinct_f_u : freshVar (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) 0 ≠ freshVar (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) 1 :=
    freshVar_injective (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) (by decide)
  have distinct_f_x : freshVar (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) 0 ≠ freshVar (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) 2 :=
    freshVar_injective (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) (by decide)
  have distinct_u_x : freshVar (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) 1 ≠ freshVar (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) 2 :=
    freshVar_injective (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) (by decide)
  ext u
  simp [syn_cwecutiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwecutisogen (R : Class) (D : Class) (S : Class) (E : Class) :
    (syn_cwecutisogen R D S E).fv = (D.fv) ∪ (E.fv) ∪ (R.fv) ∪ (S.fv) := by
  ext u
  simp [syn_cwecutisogen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwecutcardfn (R : Class) (D : Class) :
    (syn_cwecutcardfn R D).fv = (D.fv) ∪ (R.fv) := by
  have fresh_q : freshVar (R.fv ∪ D.fv) 0 ∉ (R.fv ∪ D.fv) :=
    freshVar_not_mem (R.fv ∪ D.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_q
  ext u
  simp [syn_cwecutcardfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwecutcardfactor (R : Class) (D : Class) :
    (syn_cwecutcardfactor R D).fv = (D.fv) ∪ (R.fv) := by
  ext u
  simp [syn_cwecutcardfactor, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwppgamma (F : Class) (C : Class) :
    (syn_cwppgamma F C).fv = (C.fv) ∪ (F.fv) := by
  have fresh_k : freshVar (F.fv ∪ C.fv) 0 ∉ (F.fv ∪ C.fv) :=
    freshVar_not_mem (F.fv ∪ C.fv) 0
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_k
  have fresh_m : freshVar (F.fv ∪ C.fv) 1 ∉ (F.fv ∪ C.fv) :=
    freshVar_not_mem (F.fv ∪ C.fv) 1
  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_m
  have distinct_k_m : freshVar (F.fv ∪ C.fv) 0 ≠ freshVar (F.fv ∪ C.fv) 1 :=
    freshVar_injective (F.fv ∪ C.fv) (by decide)
  ext u
  simp [syn_cwppgamma, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cio, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwppcardtfn  :
    (syn_cwppcardtfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_cwppcardtfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctcfn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwppcardt2fn  :
    (syn_cwppcardt2fn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_cwppcardt2fn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardtfn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chnbaseresfn (F : Class) :
    (syn_chnbaseresfn F).fv = F.fv := by
  ext u
  simp [syn_chnbaseresfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageresfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chncodetrnfn (F : Class) :
    (syn_chncodetrnfn F).fv = F.fv := by
  ext u
  simp [syn_chncodetrnfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnbaseresfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwppcardt4fn  :
    (syn_cwppcardt4fn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_cwppcardt4fn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardt2fn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwpppowsetfn  :
    (syn_cwpppowsetfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_cwpppowsetfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwpphwcnsetfn  :
    (syn_cwpphwcnsetfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_cwpphwcnsetfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageresfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowsetfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwpphwgendomfn  :
    (syn_cwpphwgendomfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_cwpphwgendomfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageresfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphwcnsetfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwpphwgencnvfn  :
    (syn_cwpphwgencnvfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_cwpphwgencnvfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphwgendomfn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwpphwnisosetfn  :
    (syn_cwpphwnisosetfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_cwpphwnisosetfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageresfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphwcnsetfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphwgencnvfn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwpphnpairfn  :
    (syn_cwpphnpairfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_cwpphnpairfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphwcnsetfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphwnisosetfn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwpphninputfn  :
    (syn_cwpphninputfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_cwpphninputfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphnpairfn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwppqkrelkernel  :
    (syn_cwppqkrelkernel ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_cwppqkrelkernel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwpplitphnordpointfn  :
    (syn_cwpplitphnordpointfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_cwpplitphnordpointfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwquofn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphninputfn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwpppowset2fn  :
    (syn_cwpppowset2fn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_cwpppowset2fn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowsetfn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwppfamilyrep2fn  :
    (syn_cwppfamilyrep2fn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_cwppfamilyrep2fn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpointrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwppdirecte2famfn  :
    (syn_cwppdirecte2famfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_cwppdirecte2famfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfamilyrep2fn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowset2fn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwppdirecth1famfn  :
    (syn_cwppdirecth1famfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_cwppdirecth1famfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppdirecte2famfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfamilyrep2fn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpplitphnordpointfn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwppdirecth2famfn  :
    (syn_cwppdirecth2famfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_cwppdirecth2famfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppdirecth1famfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfamilyrep2fn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpplitphnordpointfn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwppconcrete6codefn  :
    (syn_cwppconcrete6codefn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_cwppconcrete6codefn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppdirecth2famfn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwppcardt6fn  :
    (syn_cwppcardt6fn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_cwppcardt6fn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardt2fn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardt4fn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwppconcrete6fn  :
    (syn_cwppconcrete6fn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_cwppconcrete6fn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardt6fn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6codefn, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chnsicodeliftfn  :
    (syn_chnsicodeliftfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_chnsicodeliftfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwpw1secondfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwsirelfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chnsicodemap (A : Class) :
    (syn_chnsicodemap A).fv = A.fv := by
  ext u
  simp [syn_chnsicodemap, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodeliftfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chnsiquomap (A : Class) :
    (syn_chnsiquomap A).fv = A.fv := by
  ext u
  simp [syn_chnsiquomap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chncodestrictfn  :
    (syn_chncodestrictfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_chncodestrictfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clndifop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chncodepredfn  :
    (syn_chncodepredfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_chncodepredfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodestrictfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chncodecarrierfn  :
    (syn_chncodecarrierfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_chncodecarrierfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clninterop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chncodesquarefn  :
    (syn_chncodesquarefn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_chncodesquarefn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecarrierfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chncoderelfn  :
    (syn_chncoderelfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_chncoderelfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodesquarefn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clninterop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chncodecutfn  :
    (syn_chncodecutfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_chncodecutfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecarrierfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncoderelfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chncodecutpairfn  :
    (syn_chncodecutpairfn ).fv = (∅ : Finset Var) := by
  ext u
  simp [syn_chncodecutpairfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chncodecutinputs (A : Class) :
    (syn_chncodecutinputs A).fv = A.fv := by
  ext u
  simp [syn_chncodecutinputs, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwquoinputfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chncodecutrel (A : Class) :
    (syn_chncodecutrel A).fv = A.fv := by
  ext u
  simp [syn_chncodecutrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutinputs, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutpairfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chncodecmpset (A : Class) :
    (syn_chncodecmpset A).fv = A.fv := by
  ext u
  simp [syn_chncodecmpset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chncodepredinputs (A : Class) (X : Class) (v : Var) :
    (syn_chncodepredinputs A X v).fv = (A.fv) ∪ (X.fv) ∪ (({v} : Finset Var)) := by
  ext u
  simp [syn_chncodepredinputs, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_chncodepredends (A : Class) (X : Class) (v : Var) :
    (syn_chncodepredends A X v).fv = (A.fv) ∪ (X.fv) ∪ (({v} : Finset Var)) := by
  ext u
  simp [syn_chncodepredends, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredinputs, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwppstopact (F : Class) (C : Class) :
    (syn_cwppstopact F C).fv = (C.fv) ∪ (F.fv) := by
  ext u
  simp [syn_cwppstopact, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwppstopstep (F : Class) (C : Class) :
    (syn_cwppstopstep F C).fv = (C.fv) ∪ (F.fv) := by
  ext u
  simp [syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopact, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwppfreceq (F : Class) (G : Class) (I : Class) :
    (syn_cwppfreceq F G I).fv = (F.fv) ∪ (G.fv) ∪ (I.fv) := by
  ext u
  simp [syn_cwppfreceq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfix, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

theorem fv_syn_cwppfrecprefixeq (F : Class) (G : Class) (I : Class) (k : Var) :
    (syn_cwppfrecprefixeq F G I k).fv = (F.fv) ∪ (G.fv) ∪ (I.fv) ∪ (({k} : Finset Var)) := by
  ext u
  simp [syn_cwppfrecprefixeq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfreceq, Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex] <;> aesop

end NFChoice.Compiler.WPPCompactSyntaxFVExplicit
