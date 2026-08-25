import WPPCompactSyntaxFVExplicitPart007

namespace NFChoice.Compiler.WPPCompactSyntaxFVExplicit

open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-! Explicit-only FV equations for the WPP extension; no global simp attributes. -/

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

end NFChoice.Compiler.WPPCompactSyntaxFVExplicit
