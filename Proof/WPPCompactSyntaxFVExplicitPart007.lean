import WPPCompactSyntaxFVExplicitPart006

namespace NFChoice.Compiler.WPPCompactSyntaxFVExplicit

open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-! Explicit-only FV equations for the WPP extension; no global simp attributes. -/

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

end NFChoice.Compiler.WPPCompactSyntaxFVExplicit
