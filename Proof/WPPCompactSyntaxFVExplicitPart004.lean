import WPPCompactSyntaxFVExplicitPart003

namespace NFChoice.Compiler.WPPCompactSyntaxFVExplicit

open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-! Explicit-only FV equations for the WPP extension; no global simp attributes. -/

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

end NFChoice.Compiler.WPPCompactSyntaxFVExplicit
