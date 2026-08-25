import WPPCompactSyntaxFVExplicitPart008

namespace NFChoice.Compiler.WPPCompactSyntaxFVExplicit

open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-! Explicit-only FV equations for the WPP extension; no global simp attributes. -/

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

end NFChoice.Compiler.WPPCompactSyntaxFVExplicit
