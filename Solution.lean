import NFNotWPP.Surface
import NFStandard.NotWPPPrfBridge

/-!
# Proved solution: standard NF derives the negation of WPP

This module imports a clean proof-free mirror of Challenge's declaration
surface and adds the accepted proof through its solution-side dependency. WPP means the **Weak
Partition Principle**: if there are a surjection from `y` onto `x` and an
injection from `y` into `x`, then there is an injection from `x` into
`y`. The final proof first replaces every use of one of Hailperin's eleven
finite-basis axioms by its formal derivation from extensionality and stratified
comprehension, then translates all eight first-order proof constructors
structurally into the mirrored Challenge calculus.
-/

namespace NFNotWPP

open scoped NFNotWPP

/-!
This solution-only section bridges the accepted nominal source syntax and the
clean proof-free mirror of the Challenge surface. No proof objects or theory equalities
are handled here: it proves that structural quotation of nominal lowering
preserves the exact WPP formula.
-/

namespace SourceEquality

open scoped Fol

abbrev SourceLNF := NFChoice.Foundation.LNF
abbrev AcceptedClass := NFChoice.SemanticCore.Class
abbrev AcceptedWff := NFChoice.SemanticCore.Wff

/-! ## Total quotation of function-free Flypitch formulas -/

def quoteTerm : Fol.term SourceLNF -> Nat :=
  Fol.term.elim (fun k => k) (fun f _ _ => nomatch f)

@[simp] theorem quoteTerm_var (k : Nat) :
    quoteTerm (&k : Fol.term SourceLNF) = k := rfl

def quoteRelation : {l : Nat} ->
    NFChoice.Foundation.LNFRelation l ->
    DVec (Fol.term SourceLNF) l -> NFNotWPP.Formula
  | _, .mem, DVec.cons s (DVec.cons t DVec.nil) =>
      .mem (quoteTerm s) (quoteTerm t)

def quoteFormula : Fol.formula SourceLNF -> NFNotWPP.Formula :=
  Fol.formula.rec
    .falsum
    (fun s t => .equal (quoteTerm s) (quoteTerm t))
    (fun {_} R ts => quoteRelation R ts)
    (fun {_ _} p q => .imp p q)
    (fun {_} p => .all p)

@[simp] theorem quoteFormula_falsum :
    quoteFormula (Fol.preformula.falsum : Fol.formula SourceLNF) =
      .falsum := rfl

@[simp] theorem quoteFormula_equal (s t : Fol.term SourceLNF) :
    quoteFormula (Fol.preformula.equal s t) =
      .equal (quoteTerm s) (quoteTerm t) := rfl

@[simp] theorem quoteFormula_imp (p q : Fol.formula SourceLNF) :
    quoteFormula (Fol.preformula.imp p q) =
      .imp (quoteFormula p) (quoteFormula q) := rfl

@[simp] theorem quoteFormula_all (p : Fol.formula SourceLNF) :
    quoteFormula (Fol.preformula.all p) = .all (quoteFormula p) := rfl

@[simp] theorem quoteFormula_mem (s t : Fol.term SourceLNF) :
    quoteFormula
        (NFChoice.DirectNominalPrf.GenericLogicalHandlers.nfMem s t) =
      .mem (quoteTerm s) (quoteTerm t) := by
  change quoteFormula
      (Fol.apps_rel
        (Fol.preformula.rel NFChoice.Foundation.LNFRelation.mem)
        (DVec.cons s (DVec.cons t DVec.nil))) = _
  rw [quoteFormula, Fol.formula.rec_apps_rel]
  rfl

/-! ## Constructor-for-constructor map of the two nominal ASTs -/

mutual
  @[simp] def reflectClass : AcceptedClass -> NFNotWPP.Class
    | .cv x => .cv x
    | .cab x p => .cab x (reflectWff p)

  @[simp] def reflectWff : AcceptedWff -> NFNotWPP.Wff
    | .falsum => .falsum
    | .imp p q => .imp (reflectWff p) (reflectWff q)
    | .all x p => .all x (reflectWff p)
    | .objEq x y => .objEq x y
    | .objMem x y => .objMem x y
    | .classEq A B => .classEq (reflectClass A) (reflectClass B)
    | .classMem A B => .classMem (reflectClass A) (reflectClass B)
end

@[simp] theorem reflectWff_neg (p : AcceptedWff) :
    reflectWff p.neg = (reflectWff p).neg := rfl

@[simp] theorem reflect_liftRho
    (rho : NFChoice.SemanticCore.Var -> Nat) :
    NFChoice.DirectNominalPrf.Nominal.liftRho rho =
      NFNotWPP.Nominal.liftRho rho := rfl

@[simp] theorem reflect_bindRho
    (rho : NFChoice.SemanticCore.Var -> Nat) (x : Nat) :
    NFChoice.DirectNominalPrf.Nominal.bindRho rho x =
      NFNotWPP.Nominal.bindRho rho x := rfl

@[simp] theorem reflect_updateRho
    (rho : NFChoice.SemanticCore.Var -> Nat) (x value : Nat) :
    NFChoice.DirectNominalPrf.Nominal.updateRho rho x value =
      NFNotWPP.Nominal.updateRho rho x value := rfl

mutual
  @[simp] theorem reflectClass_fv (A : AcceptedClass) :
      (reflectClass A).fv = A.fv := by
    cases A with
    | cv x => rfl
    | cab x p => simp [reflectClass, NFNotWPP.Class.fv,
        NFChoice.SemanticCore.Class.fv, reflectWff_fv p]

  @[simp] theorem reflectWff_fv (p : AcceptedWff) :
      (reflectWff p).fv = p.fv := by
    cases p with
    | falsum => rfl
    | imp p q => simp [reflectWff, NFNotWPP.Wff.fv,
        NFChoice.SemanticCore.Wff.fv, reflectWff_fv p, reflectWff_fv q]
    | all x p => simp [reflectWff, NFNotWPP.Wff.fv,
        NFChoice.SemanticCore.Wff.fv, reflectWff_fv p]
    | objEq x y => rfl
    | objMem x y => rfl
    | classEq A B => simp [reflectWff, NFNotWPP.Wff.fv,
        NFChoice.SemanticCore.Wff.fv, reflectClass_fv A, reflectClass_fv B]
    | classMem A B => simp [reflectWff, NFNotWPP.Wff.fv,
        NFChoice.SemanticCore.Wff.fv, reflectClass_fv A, reflectClass_fv B]
end

/-! ## Quotation commutes with nominal lowering -/

mutual
  @[simp] theorem quote_lowerClassPred
      (rho : NFChoice.SemanticCore.Var -> Nat) (candidate : Nat)
      (A : AcceptedClass) :
      quoteFormula
          (NFChoice.DirectNominalPrf.Nominal.lowerClassPred rho candidate A) =
        NFNotWPP.Nominal.lowerClassPred rho candidate (reflectClass A) := by
    cases A with
    | cv x =>
        simp [NFChoice.DirectNominalPrf.Nominal.lowerClassPred,
          NFNotWPP.Nominal.lowerClassPred, reflectClass]
    | cab x p =>
        simp [NFChoice.DirectNominalPrf.Nominal.lowerClassPred,
          NFNotWPP.Nominal.lowerClassPred, reflectClass,
          quote_lowerWff]

  @[simp] theorem quote_lowerWff
      (rho : NFChoice.SemanticCore.Var -> Nat) (p : AcceptedWff) :
      quoteFormula (NFChoice.DirectNominalPrf.Nominal.lowerWff rho p) =
        NFNotWPP.Nominal.lowerWff rho (reflectWff p) := by
    cases p with
    | falsum => rfl
    | imp p q =>
        simp [NFChoice.DirectNominalPrf.Nominal.lowerWff,
          NFNotWPP.Nominal.lowerWff, reflectWff,
          quote_lowerWff]
    | all x p =>
        simp [NFChoice.DirectNominalPrf.Nominal.lowerWff,
          NFNotWPP.Nominal.lowerWff, reflectWff,
          quote_lowerWff]
    | objEq x y =>
        simp [NFChoice.DirectNominalPrf.Nominal.lowerWff,
          NFNotWPP.Nominal.lowerWff, reflectWff]
    | objMem x y =>
        simp [NFChoice.DirectNominalPrf.Nominal.lowerWff,
          NFNotWPP.Nominal.lowerWff, reflectWff]
    | classEq A B =>
        simp [NFChoice.DirectNominalPrf.Nominal.lowerWff,
          NFNotWPP.Nominal.lowerWff, reflectWff,
          NFChoice.DirectNominalPrf.Nominal.biimp,
          NFChoice.DirectNominalPrf.Nominal.conj,
          NFChoice.DirectNominalPrf.Nominal.neg,
          NFNotWPP.Formula.biimp, NFNotWPP.Formula.conj,
          NFNotWPP.Formula.neg, quote_lowerClassPred]
    | classMem A B =>
        simp [NFChoice.DirectNominalPrf.Nominal.lowerWff,
          NFNotWPP.Nominal.lowerWff, reflectWff,
          NFChoice.DirectNominalPrf.Nominal.ex,
          NFChoice.DirectNominalPrf.Nominal.biimp,
          NFChoice.DirectNominalPrf.Nominal.conj,
          NFChoice.DirectNominalPrf.Nominal.neg,
          NFNotWPP.Formula.ex, NFNotWPP.Formula.biimp,
          NFNotWPP.Formula.conj, NFNotWPP.Formula.neg,
          quote_lowerClassPred]
end

/-! ## Exact WPP endpoint -/

open NFChoice.Compiler

/-!
The exact WPP source depends on the following small closure of transparent
source constructors.  Recording one homomorphism lemma per constructor keeps
kernel reduction local; in particular, the endpoint below never asks Lean to
normalize both complete WPP ASTs in one step.
-/

@[simp] theorem reflect_syn_wa (p q : AcceptedWff) :
    reflectWff (CompactSourceSyntax.syn_wa p q) =
      NFNotWPP.Source.syn_wa (reflectWff p) (reflectWff q) := rfl

@[simp] theorem reflect_syn_wex (x : Nat) (p : AcceptedWff) :
    reflectWff (CompactSourceSyntax.syn_wex x p) =
      NFNotWPP.Source.syn_wex x (reflectWff p) := rfl

@[simp] theorem reflect_syn_wnan (p q : AcceptedWff) :
    reflectWff (CompactSourceSyntax.syn_wnan p q) =
      NFNotWPP.Source.syn_wnan (reflectWff p) (reflectWff q) := by
  simp [CompactSourceSyntax.syn_wnan, NFNotWPP.Source.syn_wnan]

@[simp] theorem reflect_syn_cnin (A B : AcceptedClass) :
    reflectClass (CompactSourceSyntax.syn_cnin A B) =
      NFNotWPP.Source.syn_cnin (reflectClass A) (reflectClass B) := by
  simp [CompactSourceSyntax.syn_cnin, NFNotWPP.Source.syn_cnin,
    NFChoice.ReplaySupport.freshVar, NFNotWPP.freshVar, reflectClass,
    reflectWff]

@[simp] theorem reflect_syn_ccompl (A : AcceptedClass) :
    reflectClass (CompactSourceSyntax.syn_ccompl A) =
      NFNotWPP.Source.syn_ccompl (reflectClass A) := by
  simp [CompactSourceSyntax.syn_ccompl, NFNotWPP.Source.syn_ccompl]

@[simp] theorem reflect_syn_cin (A B : AcceptedClass) :
    reflectClass (CompactSourceSyntax.syn_cin A B) =
      NFNotWPP.Source.syn_cin (reflectClass A) (reflectClass B) := by
  simp [CompactSourceSyntax.syn_cin, NFNotWPP.Source.syn_cin]

@[simp] theorem reflect_syn_cdif (A B : AcceptedClass) :
    reflectClass (CompactSourceSyntax.syn_cdif A B) =
      NFNotWPP.Source.syn_cdif (reflectClass A) (reflectClass B) := by
  simp [CompactSourceSyntax.syn_cdif, NFNotWPP.Source.syn_cdif]

@[simp] theorem reflect_syn_cvv :
    reflectClass CompactSourceSyntax.syn_cvv = NFNotWPP.Source.syn_cvv := by
  simp [CompactSourceSyntax.syn_cvv, NFNotWPP.Source.syn_cvv,
    NFChoice.ReplaySupport.freshVar, NFNotWPP.freshVar, reflectClass,
    reflectWff]

@[simp] theorem reflect_syn_c0 :
    reflectClass CompactSourceSyntax.syn_c0 = NFNotWPP.Source.syn_c0 := by
  simp [CompactSourceSyntax.syn_c0, NFNotWPP.Source.syn_c0]

@[simp] theorem reflect_syn_csn (A : AcceptedClass) :
    reflectClass (CompactSourceSyntax.syn_csn A) =
      NFNotWPP.Source.syn_csn (reflectClass A) := by
  simp [CompactSourceSyntax.syn_csn, NFNotWPP.Source.syn_csn,
    NFChoice.ReplaySupport.freshVar, NFNotWPP.freshVar, reflectClass,
    reflectWff]

@[simp] theorem reflect_syn_c0c :
    reflectClass CompactSourceSyntax.syn_c0c = NFNotWPP.Source.syn_c0c := by
  simp [CompactSourceSyntax.syn_c0c, NFNotWPP.Source.syn_c0c]

@[simp] theorem reflect_syn_c1c :
    reflectClass CompactSourceSyntax.syn_c1c = NFNotWPP.Source.syn_c1c := by
  simp [CompactSourceSyntax.syn_c1c, NFNotWPP.Source.syn_c1c,
    NFChoice.ReplaySupport.freshVar, NFNotWPP.freshVar, reflectClass,
    reflectWff]

@[simp] theorem reflect_syn_wo (p q : AcceptedWff) :
    reflectWff (CompactSourceSyntax.syn_wo p q) =
      NFNotWPP.Source.syn_wo (reflectWff p) (reflectWff q) := rfl

@[simp] theorem reflect_syn_cif
    (p : AcceptedWff) (A B : AcceptedClass) :
    reflectClass (CompactSourceSyntax.syn_cif p A B) =
      NFNotWPP.Source.syn_cif (reflectWff p) (reflectClass A)
        (reflectClass B) := by
  simp [CompactSourceSyntax.syn_cif, NFNotWPP.Source.syn_cif,
    NFChoice.ReplaySupport.freshVar, NFNotWPP.freshVar, reflectClass,
    reflectWff]

@[simp] theorem reflect_syn_cint (A : AcceptedClass) :
    reflectClass (CompactSourceSyntax.syn_cint A) =
      NFNotWPP.Source.syn_cint (reflectClass A) := by
  simp [CompactSourceSyntax.syn_cint, NFNotWPP.Source.syn_cint,
    NFChoice.ReplaySupport.freshVar, NFNotWPP.freshVar, reflectClass,
    reflectWff]

@[simp] theorem reflect_syn_cun (A B : AcceptedClass) :
    reflectClass (CompactSourceSyntax.syn_cun A B) =
      NFNotWPP.Source.syn_cun (reflectClass A) (reflectClass B) := by
  simp [CompactSourceSyntax.syn_cun, NFNotWPP.Source.syn_cun]

@[simp] theorem reflect_syn_wrex
    (x : Nat) (A : AcceptedClass) (p : AcceptedWff) :
    reflectWff (CompactSourceSyntax.syn_wrex x A p) =
      NFNotWPP.Source.syn_wrex x (reflectClass A) (reflectWff p) := by
  simp [CompactSourceSyntax.syn_wrex, NFNotWPP.Source.syn_wrex]

@[simp] theorem reflect_syn_cplc (A B : AcceptedClass) :
    reflectClass (CompactSourceSyntax.syn_cplc A B) =
      NFNotWPP.Source.syn_cplc (reflectClass A) (reflectClass B) := by
  simp [CompactSourceSyntax.syn_cplc, NFNotWPP.Source.syn_cplc,
    NFChoice.ReplaySupport.freshVar, NFNotWPP.freshVar, reflectClass,
    reflectWff]

@[simp] theorem reflect_syn_wral
    (x : Nat) (A : AcceptedClass) (p : AcceptedWff) :
    reflectWff (CompactSourceSyntax.syn_wral x A p) =
      NFNotWPP.Source.syn_wral x (reflectClass A) (reflectWff p) := rfl

@[simp] theorem reflect_syn_cnnc :
    reflectClass CompactSourceSyntax.syn_cnnc = NFNotWPP.Source.syn_cnnc := by
  simp [CompactSourceSyntax.syn_cnnc, NFNotWPP.Source.syn_cnnc,
    NFChoice.ReplaySupport.freshVar, NFNotWPP.freshVar]

@[simp] theorem reflect_syn_cphi (A : AcceptedClass) :
    reflectClass (CompactSourceSyntax.syn_cphi A) =
      NFNotWPP.Source.syn_cphi (reflectClass A) := by
  simp [CompactSourceSyntax.syn_cphi, NFNotWPP.Source.syn_cphi,
    NFChoice.ReplaySupport.freshVar, NFNotWPP.freshVar, reflectClass,
    reflectWff]

@[simp] theorem reflect_syn_cop (A B : AcceptedClass) :
    reflectClass (CompactSourceSyntax.syn_cop A B) =
      NFNotWPP.Source.syn_cop (reflectClass A) (reflectClass B) := by
  simp [CompactSourceSyntax.syn_cop, NFNotWPP.Source.syn_cop,
    NFChoice.ReplaySupport.freshVar, NFNotWPP.freshVar, reflectClass,
    reflectWff]

@[simp] theorem reflect_syn_copab
    (x y : Nat) (p : AcceptedWff) :
    reflectClass (CompactSourceSyntax.syn_copab x y p) =
      NFNotWPP.Source.syn_copab x y (reflectWff p) := by
  simp [CompactSourceSyntax.syn_copab, NFNotWPP.Source.syn_copab,
    NFChoice.ReplaySupport.freshVar, NFNotWPP.freshVar, reflectClass,
    reflectWff]

@[simp] theorem reflect_syn_wbr (A R B : AcceptedClass) :
    reflectWff (CompactSourceSyntax.syn_wbr A R B) =
      NFNotWPP.Source.syn_wbr (reflectClass A) (reflectClass R)
        (reflectClass B) := by
  simp [CompactSourceSyntax.syn_wbr, NFNotWPP.Source.syn_wbr, reflectWff]

@[simp] theorem reflect_syn_ccnv (A : AcceptedClass) :
    reflectClass (CompactSourceSyntax.syn_ccnv A) =
      NFNotWPP.Source.syn_ccnv (reflectClass A) := by
  simp [CompactSourceSyntax.syn_ccnv, NFNotWPP.Source.syn_ccnv,
    NFChoice.ReplaySupport.freshVar, NFNotWPP.freshVar]

@[simp] theorem reflect_syn_cima (A B : AcceptedClass) :
    reflectClass (CompactSourceSyntax.syn_cima A B) =
      NFNotWPP.Source.syn_cima (reflectClass A) (reflectClass B) := by
  simp [CompactSourceSyntax.syn_cima, NFNotWPP.Source.syn_cima,
    NFChoice.ReplaySupport.freshVar, NFNotWPP.freshVar, reflectClass]

@[simp] theorem reflect_syn_crn (A : AcceptedClass) :
    reflectClass (CompactSourceSyntax.syn_crn A) =
      NFNotWPP.Source.syn_crn (reflectClass A) := by
  simp [CompactSourceSyntax.syn_crn, NFNotWPP.Source.syn_crn]

@[simp] theorem reflect_syn_cdm (A : AcceptedClass) :
    reflectClass (CompactSourceSyntax.syn_cdm A) =
      NFNotWPP.Source.syn_cdm (reflectClass A) := by
  simp [CompactSourceSyntax.syn_cdm, NFNotWPP.Source.syn_cdm]

@[simp] theorem reflect_syn_ccom (A B : AcceptedClass) :
    reflectClass (CompactSourceSyntax.syn_ccom A B) =
      NFNotWPP.Source.syn_ccom (reflectClass A) (reflectClass B) := by
  simp [CompactSourceSyntax.syn_ccom, NFNotWPP.Source.syn_ccom,
    NFChoice.ReplaySupport.freshVar, NFNotWPP.freshVar]

@[simp] theorem reflect_syn_cid :
    reflectClass CompactSourceSyntax.syn_cid = NFNotWPP.Source.syn_cid := by
  simp [CompactSourceSyntax.syn_cid, NFNotWPP.Source.syn_cid,
    NFChoice.ReplaySupport.freshVar, NFNotWPP.freshVar]

@[simp] theorem reflect_syn_wss (A B : AcceptedClass) :
    reflectWff (CompactSourceSyntax.syn_wss A B) =
      NFNotWPP.Source.syn_wss (reflectClass A) (reflectClass B) := by
  simp [CompactSourceSyntax.syn_wss, NFNotWPP.Source.syn_wss, reflectWff]

@[simp] theorem reflect_syn_wfun (A : AcceptedClass) :
    reflectWff (CompactSourceSyntax.syn_wfun A) =
      NFNotWPP.Source.syn_wfun (reflectClass A) := by
  simp [CompactSourceSyntax.syn_wfun, NFNotWPP.Source.syn_wfun]

@[simp] theorem reflect_syn_wfn (A B : AcceptedClass) :
    reflectWff (CompactSourceSyntax.syn_wfn A B) =
      NFNotWPP.Source.syn_wfn (reflectClass A) (reflectClass B) := by
  simp [CompactSourceSyntax.syn_wfn, NFNotWPP.Source.syn_wfn]

@[simp] theorem reflect_syn_wf (F A B : AcceptedClass) :
    reflectWff (CompactSourceSyntax.syn_wf F A B) =
      NFNotWPP.Source.syn_wf (reflectClass F) (reflectClass A)
        (reflectClass B) := by
  simp [CompactSourceSyntax.syn_wf, NFNotWPP.Source.syn_wf]

@[simp] theorem reflect_syn_wf1 (F A B : AcceptedClass) :
    reflectWff (CompactSourceSyntax.syn_wf1 F A B) =
      NFNotWPP.Source.syn_wf1 (reflectClass F) (reflectClass A)
        (reflectClass B) := by
  simp [CompactSourceSyntax.syn_wf1, NFNotWPP.Source.syn_wf1]

@[simp] theorem reflect_syn_wfo (F A B : AcceptedClass) :
    reflectWff (CompactSourceSyntax.syn_wfo F A B) =
      NFNotWPP.Source.syn_wfo (reflectClass F) (reflectClass A)
        (reflectClass B) := by
  simp [CompactSourceSyntax.syn_wfo, NFNotWPP.Source.syn_wfo]

theorem reflect_sourceWPP :
    reflectWff NFChoice.Compiler.CompactSourceSyntax.syn_wwpp =
      NFNotWPP.Source.syn_wwpp := by
  simp [CompactSourceSyntax.syn_wwpp, NFNotWPP.Source.syn_wwpp,
    NFChoice.ReplaySupport.freshVar, NFNotWPP.freshVar, reflectWff]

theorem quote_accepted_sourceWPP :
    quoteFormula
        (NFChoice.DirectNominalPrf.Nominal.lowerWff id
          NFChoice.Compiler.CompactSourceSyntax.syn_wwpp) =
      NFNotWPP.SourceWPPFOL := by
  calc
    quoteFormula
        (NFChoice.DirectNominalPrf.Nominal.lowerWff id
          NFChoice.Compiler.CompactSourceSyntax.syn_wwpp) =
        NFNotWPP.Nominal.lowerWff id
          (reflectWff NFChoice.Compiler.CompactSourceSyntax.syn_wwpp) :=
      quote_lowerWff id NFChoice.Compiler.CompactSourceSyntax.syn_wwpp
    _ = NFNotWPP.Nominal.lowerWff id NFNotWPP.Source.syn_wwpp :=
      congrArg (NFNotWPP.Nominal.lowerWff id) reflect_sourceWPP
    _ = NFNotWPP.SourceWPPFOL := rfl

end SourceEquality

/-!
Theory-identification layer for the Palomar solution. It quotes the accepted
standard NF schema into the mirrored Challenge schema; the
eleven finite-basis formulas remain available as the internal bridge used to
construct the source derivation.
-/

namespace TheoryBridgeProbe

open scoped Fol

abbrev SourceLNF := NFChoice.Foundation.LNF
abbrev SourceName := NFChoice.Foundation.HailperinAxiomName

def quoteTerm : Fol.term SourceLNF -> Nat :=
  Fol.term.elim (fun k => k) (fun f _ _ => nomatch f)

def quoteFormula (f : Fol.formula SourceLNF) : NFNotWPP.Formula :=
  Fol.formula.rec (C := fun _ => NFNotWPP.Formula)
    NFNotWPP.Formula.falsum
    (fun s t => NFNotWPP.Formula.equal (quoteTerm s) (quoteTerm t))
    (fun {l} (R : SourceLNF.relations l) (ts : DVec (Fol.term SourceLNF) l) =>
      match R, ts with
      | NFChoice.Foundation.LNFRelation.mem,
          DVec.cons s (DVec.cons t DVec.nil) =>
        NFNotWPP.Formula.mem (quoteTerm s) (quoteTerm t))
    (fun {_f _g} (p q : NFNotWPP.Formula) => NFNotWPP.Formula.imp p q)
    (fun {_f} (p : NFNotWPP.Formula) => NFNotWPP.Formula.all p)
    f

@[simp] theorem quoteTerm_var (k : Nat) :
    quoteTerm (&k : Fol.term SourceLNF) = k := rfl

@[simp] theorem quoteFormula_falsum :
    quoteFormula (Fol.preformula.falsum : Fol.formula SourceLNF) =
      NFNotWPP.Formula.falsum := rfl

@[simp] theorem quoteFormula_equal (s t : Fol.term SourceLNF) :
    quoteFormula (Fol.preformula.equal s t) =
      NFNotWPP.Formula.equal (quoteTerm s) (quoteTerm t) := rfl

@[simp] theorem quoteFormula_imp (p q : Fol.formula SourceLNF) :
    quoteFormula (Fol.preformula.imp p q) =
      NFNotWPP.Formula.imp (quoteFormula p) (quoteFormula q) := rfl

@[simp] theorem quoteFormula_all (p : Fol.formula SourceLNF) :
    quoteFormula (Fol.preformula.all p) =
      NFNotWPP.Formula.all (quoteFormula p) := rfl

@[simp] theorem quoteFormula_mem (s t : Fol.term SourceLNF) :
    quoteFormula
        (Fol.preformula.apprel
          (Fol.preformula.apprel
            (Fol.preformula.rel NFChoice.Foundation.LNFRelation.mem) s) t) =
      NFNotWPP.Formula.mem (quoteTerm s) (quoteTerm t) := by
  change quoteFormula
      (Fol.apps_rel
        (Fol.preformula.rel NFChoice.Foundation.LNFRelation.mem)
        (DVec.cons s (DVec.cons t DVec.nil))) = _
  unfold quoteFormula
  rw [Fol.formula.rec_apps_rel]
  simp

/-- Constructor-for-constructor quotation before the source boundedness proof
is erased. -/
def quoteBFormula : {n : Nat} -> NFChoice.Foundation.Formula n ->
    NFNotWPP.BFormula n
  | _, .falsum => .falsum
  | _, .equal x y => .equal x y
  | _, .mem x y => .mem x y
  | _, .imp p q => .imp (quoteBFormula p) (quoteBFormula q)
  | _, .all p => .all (quoteBFormula p)

/-- Quotation commutes with the accepted front end's translation to Flypitch. -/
theorem quoteFormula_toFlypitch {n : Nat}
    (p : NFChoice.Foundation.Formula n) :
    quoteFormula (NFChoice.Foundation.Formula.toFlypitch p).fst =
      NFNotWPP.BFormula.erase (quoteBFormula p) := by
  induction p with
  | falsum => rfl
  | equal x y => rfl
  | mem x y =>
      change quoteFormula
          (Fol.preformula.apprel
            (Fol.preformula.apprel
              (Fol.preformula.rel NFChoice.Foundation.LNFRelation.mem)
              (&x.val)) (&y.val)) = _
      simp [quoteBFormula, NFNotWPP.BFormula.erase]
  | imp p q ihp ihq =>
      change quoteFormula
          (Fol.preformula.imp p.toFlypitch.fst q.toFlypitch.fst) = _
      simp [quoteBFormula, NFNotWPP.BFormula.erase, ihp, ihq]
  | all p ih =>
      change quoteFormula (Fol.preformula.all p.toFlypitch.fst) = _
      simp [quoteBFormula, NFNotWPP.BFormula.erase, ih]

/-- Inverse quotation of the challenge's intrinsically scoped syntax. -/
def unquoteBFormula : {n : Nat} -> NFNotWPP.BFormula n ->
    NFChoice.Foundation.Formula n
  | _, .falsum => .falsum
  | _, .equal x y => .equal x y
  | _, .mem x y => .mem x y
  | _, .imp p q => .imp (unquoteBFormula p) (unquoteBFormula q)
  | _, .all p => .all (unquoteBFormula p)

@[simp] theorem quoteBFormula_unquoteBFormula {n : Nat}
    (p : NFNotWPP.BFormula n) :
    quoteBFormula (unquoteBFormula p) = p := by
  induction p with
  | falsum => rfl
  | equal => rfl
  | mem => rfl
  | imp p q ihp ihq => simp [quoteBFormula, unquoteBFormula, ihp, ihq]
  | all p ih => simp [quoteBFormula, unquoteBFormula, ih]

@[simp] theorem unquoteBFormula_quoteBFormula {n : Nat}
    (p : NFChoice.Foundation.Formula n) :
    unquoteBFormula (quoteBFormula p) = p := by
  induction p with
  | falsum => rfl
  | equal => rfl
  | mem => rfl
  | imp p q ihp ihq => simp [quoteBFormula, unquoteBFormula, ihp, ihq]
  | all p ih => simp [quoteBFormula, unquoteBFormula, ih]

/-- Quotation commutes with the intrinsic renaming used by comprehension. -/
theorem quoteBFormula_renameVars {n m : Nat} (rho : Fin n -> Fin m)
    (p : NFChoice.Foundation.Formula n) :
    quoteBFormula
        (NFChoice.Foundation.ExactLiteralTrial.Formula.renameVars rho p) =
      NFNotWPP.BFormula.renameVars rho (quoteBFormula p) := by
  induction p generalizing m with
  | falsum => rfl
  | equal => rfl
  | mem => rfl
  | imp p q ihp ihq =>
      simp [NFChoice.Foundation.ExactLiteralTrial.Formula.renameVars,
        NFNotWPP.BFormula.renameVars, quoteBFormula, ihp, ihq]
  | all p ih =>
      simp [NFChoice.Foundation.ExactLiteralTrial.Formula.renameVars,
        NFNotWPP.BFormula.renameVars, quoteBFormula, ih]

/-- Quotation preserves every fixed integer stratification assignment. -/
theorem quoteBFormula_stratifiedBy {n : Nat} (ty : Fin n -> Int)
    (p : NFChoice.Foundation.Formula n) :
    NFNotWPP.BFormula.StratifiedBy ty (quoteBFormula p) ↔
      NFChoice.Foundation.Formula.StratifiedBy ty p := by
  induction p with
  | falsum => rfl
  | equal => rfl
  | mem => rfl
  | imp p q ihp ihq =>
      exact and_congr (ihp ty) (ihq ty)
  | all p ih =>
      exact exists_congr (fun k => ih (Fin.cases k ty))

/-- Quotation preserves existence of a stratification assignment. -/
theorem quoteBFormula_stratified {n : Nat}
    (p : NFChoice.Foundation.Formula n) :
    NFNotWPP.BFormula.Stratified (quoteBFormula p) ↔
      NFChoice.Foundation.Formula.Stratified p := by
  simp only [NFNotWPP.BFormula.Stratified,
    NFChoice.Foundation.Formula.Stratified]
  exact exists_congr (fun ty => quoteBFormula_stratifiedBy ty p)

/-- The inverse quotation also preserves stratification. -/
theorem unquoteBFormula_stratified {n : Nat}
    (p : NFNotWPP.BFormula n) :
    NFChoice.Foundation.Formula.Stratified (unquoteBFormula p) ↔
      NFNotWPP.BFormula.Stratified p := by
  rw [← quoteBFormula_stratified]
  simp

/-- Quotation commutes with the open comprehension body. -/
theorem quoteBFormula_comprehensionBody {n : Nat}
    (p : NFChoice.Foundation.Formula (n + 1)) :
    quoteBFormula (NFChoice.Foundation.NFStandard.comprehensionBody p) =
      NFNotWPP.comprehensionBody (quoteBFormula p) := by
  simp [NFChoice.Foundation.NFStandard.comprehensionBody,
    NFNotWPP.comprehensionBody,
    NFChoice.Foundation.ExactLiteralTrial.Formula.eqCandidateToPredicate,
    NFChoice.Foundation.ExactLiteralTrial.Formula.liftClassPredicate,
    NFNotWPP.BFormula.eqCandidateToPredicate,
    NFNotWPP.BFormula.liftClassPredicate,
    NFChoice.Foundation.Formula.ex, NFNotWPP.BFormula.ex,
    NFChoice.Foundation.Formula.neg, NFNotWPP.BFormula.neg,
    NFChoice.Foundation.Formula.biimp, NFNotWPP.BFormula.biimp,
    NFChoice.Foundation.Formula.conj, NFNotWPP.BFormula.conj,
    quoteBFormula, quoteBFormula_renameVars]

/-- Erasing bounded universal closure gives ordinary repeated closure. -/
theorem fst_bd_alls : ∀ (n : Nat) (p : Fol.bounded_formula SourceLNF n),
    (Fol.bd_alls n p).fst = Fol.alls n p.fst := by
  intro n
  induction n with
  | zero => intro p; rfl
  | succ n ih =>
      intro p
      simp only [Fol.bd_alls]
      rw [ih (Fol.bd_all p)]
      change Fol.alls n (Fol.preformula.all p.fst) = _
      rw [Fol.alls_all_commute]
      rfl

/-- Quotation commutes with repeated universal closure. -/
theorem quoteFormula_alls (n : Nat) (p : Fol.formula SourceLNF) :
    quoteFormula (Fol.alls n p) =
      NFNotWPP.Formula.alls n (quoteFormula p) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Fol.alls, NFNotWPP.Formula.alls, ih]

/-- Quotation commutes with each standard NF comprehension instance. -/
theorem quote_comprehensionInstance {n : Nat}
    (p : NFChoice.Foundation.Formula (n + 1)) :
    quoteFormula
        (NFChoice.Foundation.NFStandard.comprehensionInstance p).fst =
      NFNotWPP.comprehensionInstance (quoteBFormula p) := by
  rw [NFChoice.Foundation.NFStandard.comprehensionInstance,
    NFChoice.Foundation.Formula.closeAll]
  rw [fst_bd_alls]
  rw [quoteFormula_alls, quoteFormula_toFlypitch,
    quoteBFormula_comprehensionBody]
  rfl

/-- The constructor-for-constructor identification of the two finite indexes. -/
def quoteName : SourceName -> NFNotWPP.HailperinAxiomName
  | .axExt => .axExt
  | .axNin => .axNin
  | .axXp => .axXp
  | .axCnv => .axCnv
  | .ax1c => .ax1c
  | .axSset => .axSset
  | .axSi => .axSi
  | .axIns2 => .axIns2
  | .axIns3 => .axIns3
  | .axTypeLower => .axTypeLower
  | .axSn => .axSn

/-- The inverse constructor-for-constructor identification. -/
def unquoteName : NFNotWPP.HailperinAxiomName -> SourceName
  | .axExt => .axExt
  | .axNin => .axNin
  | .axXp => .axXp
  | .axCnv => .axCnv
  | .ax1c => .ax1c
  | .axSset => .axSset
  | .axSi => .axSi
  | .axIns2 => .axIns2
  | .axIns3 => .axIns3
  | .axTypeLower => .axTypeLower
  | .axSn => .axSn

@[simp] theorem quoteName_unquoteName (name : NFNotWPP.HailperinAxiomName) :
    quoteName (unquoteName name) = name := by
  cases name <;> rfl

@[simp] theorem unquoteName_quoteName (name : SourceName) :
    unquoteName (quoteName name) = name := by
  cases name <;> rfl

set_option linter.unusedSimpArgs false in
/--
Each accepted literal source sentence, after forgetting its boundedness proof
and quoting the Flypitch syntax, is definitionally the matching challenge
sentence.
-/
theorem quote_literalAxiomFormula (name : SourceName) :
    quoteFormula
        (NFChoice.Foundation.ExactLiteralTrial.literalAxiomFormula name).fst =
      NFNotWPP.literalAxiomFormula (quoteName name) := by
  rw [NFChoice.Foundation.ExactLiteralTrial.literalAxiomFormula,
    quoteFormula_toFlypitch]
  cases name <;>
    set_option maxRecDepth 100000 in
    simp [quoteName, quoteBFormula,
      NFChoice.Foundation.ExactLiteralTrial.literalAxiomSyntax,
      NFChoice.Foundation.ExactLiteralTrial.literalAxExt,
      NFChoice.Foundation.ExactLiteralTrial.literalAxNin,
      NFChoice.Foundation.ExactLiteralTrial.literalAxXp,
      NFChoice.Foundation.ExactLiteralTrial.literalAxCnv,
      NFChoice.Foundation.ExactLiteralTrial.literalAx1c,
      NFChoice.Foundation.ExactLiteralTrial.literalAxSset,
      NFChoice.Foundation.ExactLiteralTrial.literalAxSi,
      NFChoice.Foundation.ExactLiteralTrial.literalAxIns2,
      NFChoice.Foundation.ExactLiteralTrial.literalAxIns3,
      NFChoice.Foundation.ExactLiteralTrial.literalAxTypeLower,
      NFChoice.Foundation.ExactLiteralTrial.literalAxSn,
      NFChoice.Foundation.ExactLiteralTrial.literalSingleton,
      NFChoice.Foundation.ExactLiteralTrial.literalUnorderedPair,
      NFChoice.Foundation.ExactLiteralTrial.literalKPair,
      NFChoice.Foundation.ExactLiteralTrial.literalPairMem,
      NFChoice.Foundation.ExactLiteralTrial.literalDoubleSingleton,
      NFChoice.Foundation.ExactLiteralTrial.literalSingletonPairMem,
      NFChoice.Foundation.ExactLiteralTrial.literalInsertedPairMem,
      NFChoice.Foundation.ExactLiteralTrial.literalPairSingletonSecondMem,
      NFChoice.Foundation.ExactLiteralTrial.LiteralClass.membership,
      NFChoice.Foundation.ExactLiteralTrial.LiteralClass.classEq,
      NFChoice.Foundation.ExactLiteralTrial.LiteralClass.setEqClass,
      NFChoice.Foundation.ExactLiteralTrial.LiteralClass.classMemSet,
      NFChoice.Foundation.ExactLiteralTrial.Formula.eqCandidateToPredicate,
      NFChoice.Foundation.ExactLiteralTrial.Formula.liftClassPredicate,
      NFChoice.Foundation.ExactLiteralTrial.Formula.renameVars,
      NFChoice.Foundation.Formula.neg, NFChoice.Foundation.Formula.conj,
      NFChoice.Foundation.Formula.disj, NFChoice.Foundation.Formula.biimp,
      NFChoice.Foundation.Formula.ex, NFChoice.Foundation.Formula.singleton,
      NFChoice.Foundation.Formula.subset,
      NFChoice.Foundation.Formula.isSomeSingleton,
      NFNotWPP.literalAxiomFormula, NFNotWPP.literalAxiomSyntax,
      NFNotWPP.literalAxExt, NFNotWPP.literalAxNin,
      NFNotWPP.literalAxXp, NFNotWPP.literalAxCnv,
      NFNotWPP.literalAx1c, NFNotWPP.literalAxSset,
      NFNotWPP.literalAxSi, NFNotWPP.literalAxIns2,
      NFNotWPP.literalAxIns3, NFNotWPP.literalAxTypeLower,
      NFNotWPP.literalAxSn, NFNotWPP.literalSingleton,
      NFNotWPP.literalUnorderedPair, NFNotWPP.literalKPair,
      NFNotWPP.literalPairMem, NFNotWPP.literalDoubleSingleton,
      NFNotWPP.literalSingletonPairMem, NFNotWPP.literalInsertedPairMem,
      NFNotWPP.literalPairSingletonSecondMem,
      NFNotWPP.LiteralClass.membership, NFNotWPP.LiteralClass.classEq,
      NFNotWPP.LiteralClass.setEqClass, NFNotWPP.LiteralClass.classMemSet,
      NFNotWPP.BFormula.eqCandidateToPredicate,
      NFNotWPP.BFormula.liftClassPredicate,
      NFNotWPP.BFormula.renameVars, NFNotWPP.BFormula.neg,
      NFNotWPP.BFormula.conj, NFNotWPP.BFormula.disj,
      NFNotWPP.BFormula.biimp, NFNotWPP.BFormula.ex,
      NFNotWPP.BFormula.singleton, NFNotWPP.BFormula.subset,
      NFNotWPP.BFormula.isSomeSingleton, NFNotWPP.BFormula.erase]

/-- The exact quoted image of the accepted proof theory is the challenge theory. -/
theorem quote_sourceTheory :
    quoteFormula ''
        NFChoice.Foundation.ExactLiteralTrial.LiteralHailperinNF.fst =
      NFNotWPP.LiteralHailperinNF := by
  ext p
  constructor
  · rintro ⟨q, ⟨s, hs, rfl⟩, rfl⟩
    rcases hs with ⟨name, rfl⟩
    exact ⟨quoteName name, (quote_literalAxiomFormula name).symm⟩
  · rintro ⟨name, rfl⟩
    let sourceSentence :=
      NFChoice.Foundation.ExactLiteralTrial.literalAxiomFormula
        (unquoteName name)
    refine ⟨sourceSentence.fst, ?_, ?_⟩
    · exact ⟨sourceSentence, ⟨unquoteName name, rfl⟩, rfl⟩
    · simpa [sourceSentence] using
        quote_literalAxiomFormula (unquoteName name)

/-- The exact quoted image of standard NF is the challenge's standard NF. -/
theorem quote_NF :
    quoteFormula '' NFChoice.Foundation.NF.fst = NFNotWPP.NF := by
  ext q
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    rcases hs with rfl | hs
    · apply Set.mem_insert_iff.mpr
      left
      simpa [NFNotWPP.literalAxiomFormula,
        NFNotWPP.literalAxiomSyntax] using
        quote_literalAxiomFormula (.axExt : SourceName)
    · apply Set.mem_insert_iff.mpr
      right
      rcases hs with ⟨n, p, hp, rfl⟩
      exact ⟨n, quoteBFormula p,
        (quoteBFormula_stratified p).2 hp,
        quote_comprehensionInstance p⟩
  · intro hq
    rcases Set.mem_insert_iff.mp hq with hq | hq
    · subst q
      let s := NFChoice.Foundation.ExactLiteralTrial.literalAxiomFormula
        (.axExt : SourceName)
      refine ⟨s.fst, ?_, ?_⟩
      · exact ⟨s, NFChoice.Foundation.NFStandard.extensionality_mem_NF, rfl⟩
      · simpa [s, NFNotWPP.literalAxiomFormula,
          NFNotWPP.literalAxiomSyntax] using
          quote_literalAxiomFormula (.axExt : SourceName)
    · rcases hq with ⟨n, p, hp, rfl⟩
      let p' : NFChoice.Foundation.Formula (n + 1) :=
        unquoteBFormula p
      let s := NFChoice.Foundation.NFStandard.comprehensionInstance p'
      refine ⟨s.fst, ?_, ?_⟩
      · refine ⟨s, Set.mem_insert_of_mem _ ?_, rfl⟩
        exact ⟨n, p', (unquoteBFormula_stratified p).2 hp, rfl⟩
      · simpa [s, p'] using quote_comprehensionInstance p'

end TheoryBridgeProbe

/-!
Generic solution-only bridge from the accepted Flypitch derivation to the small
Challenge calculus. The exact public theorem below instantiates this structural
translator after the finite-basis axiom uses have been replaced by NF proofs.
-/

namespace SolutionBridge

open scoped Fol

abbrev SourceLNF := NFChoice.Foundation.LNF

/-! ## Total quotation of the function-free Flypitch syntax -/

def quoteTerm : Fol.term SourceLNF -> Nat :=
  Fol.term.elim (fun k => k) (fun f _ _ => nomatch f)

@[simp] theorem quoteTerm_var (k : Nat) :
    quoteTerm (&k : Fol.term SourceLNF) = k := rfl

def quoteRelation : {l : Nat} ->
    NFChoice.Foundation.LNFRelation l ->
    DVec (Fol.term SourceLNF) l -> NFNotWPP.Formula
  | _, .mem, DVec.cons s (DVec.cons t DVec.nil) =>
      .mem (quoteTerm s) (quoteTerm t)

def quoteFormula : Fol.formula SourceLNF -> NFNotWPP.Formula :=
  Fol.formula.rec
    .falsum
    (fun s t => .equal (quoteTerm s) (quoteTerm t))
    (fun {_} R ts => quoteRelation R ts)
    (fun {_ _} p q => .imp p q)
    (fun {_} p => .all p)

@[simp] theorem quoteFormula_falsum :
    quoteFormula (Fol.preformula.falsum : Fol.formula SourceLNF) = .falsum := rfl

@[simp] theorem quoteFormula_equal (s t : Fol.term SourceLNF) :
    quoteFormula (Fol.preformula.equal s t) =
      .equal (quoteTerm s) (quoteTerm t) := rfl

@[simp] theorem quoteFormula_imp (p q : Fol.formula SourceLNF) :
    quoteFormula (Fol.preformula.imp p q) =
      .imp (quoteFormula p) (quoteFormula q) := rfl

@[simp] theorem quoteFormula_all (p : Fol.formula SourceLNF) :
    quoteFormula (Fol.preformula.all p) = .all (quoteFormula p) := rfl

@[simp] theorem quoteFormula_mem (s t : Fol.term SourceLNF) :
    quoteFormula
        (NFChoice.DirectNominalPrf.GenericLogicalHandlers.nfMem s t) =
      .mem (quoteTerm s) (quoteTerm t) := by
  change quoteFormula
      (Fol.apps_rel
        (Fol.preformula.rel NFChoice.Foundation.LNFRelation.mem)
        (DVec.cons s (DVec.cons t DVec.nil))) = _
  rw [quoteFormula, Fol.formula.rec_apps_rel]
  rfl

/-! ## Exact interaction with lifting and substitution -/

@[simp] theorem quoteTerm_liftAt (t : Fol.term SourceLNF) (n m : Nat) :
    quoteTerm (Fol.lift_term_at t n m) =
      Formula.liftTermAt (quoteTerm t) n m := by
  induction t using Fol.term.rec with
  | hvar k => rfl
  | hfunc f _ _ => exact nomatch f

@[simp] theorem quoteTerm_subst (t s : Fol.term SourceLNF) (n : Nat) :
    quoteTerm (Fol.subst_term t s n) =
      Formula.substTerm (quoteTerm t) (quoteTerm s) n := by
  induction t using Fol.term.rec with
  | hvar k =>
      by_cases hkn : k < n
      · simp [Fol.subst_term, Fol.subst_realize, Formula.substTerm, hkn]
      · by_cases hnk : n < k
        · simp [Fol.subst_term, Fol.subst_realize, Formula.substTerm, hkn, hnk]
        · have h : k = n := Nat.le_antisymm (Nat.le_of_not_gt hnk) (Nat.le_of_not_gt hkn)
          subst k
          simp [Fol.subst_term, Fol.subst_realize, Formula.substTerm]
  | hfunc f _ _ => exact nomatch f

@[simp] theorem quoteFormula_liftAt (p : Fol.formula SourceLNF) (n m : Nat) :
    quoteFormula (Fol.lift_formula_at p n m) =
      Formula.liftAt (quoteFormula p) n m := by
  induction p using Fol.formula.rec generalizing m with
  | hfalsum => rfl
  | hequal s t => simp [Formula.liftAt]
  | hrel R ts =>
      cases R with
      | mem =>
        cases ts with
        | cons s ts =>
          cases ts with
          | cons t ts =>
            cases ts
            change quoteFormula
                (NFChoice.DirectNominalPrf.GenericLogicalHandlers.nfMem
                  (Fol.lift_term_at s n m) (Fol.lift_term_at t n m)) =
              Formula.liftAt
                (quoteFormula
                  (NFChoice.DirectNominalPrf.GenericLogicalHandlers.nfMem s t)) n m
            simp [Formula.liftAt]
  | himp ihp ihq => simp [Formula.liftAt, ihp, ihq]
  | hall ih => simp [Formula.liftAt, ih (m := m + 1)]

@[simp] theorem quoteFormula_subst (p : Fol.formula SourceLNF)
    (s : Fol.term SourceLNF) (n : Nat) :
    quoteFormula (Fol.subst_formula p s n) =
      Formula.substAt (quoteFormula p) (quoteTerm s) n := by
  induction p using Fol.formula.rec generalizing n with
  | hfalsum => rfl
  | hequal t u => simp [Formula.substAt]
  | hrel R ts =>
      cases R with
      | mem =>
        cases ts with
        | cons t ts =>
          cases ts with
          | cons u ts =>
            cases ts
            change quoteFormula
                (NFChoice.DirectNominalPrf.GenericLogicalHandlers.nfMem
                  (Fol.subst_term t s n) (Fol.subst_term u s n)) =
              Formula.substAt
                (quoteFormula
                  (NFChoice.DirectNominalPrf.GenericLogicalHandlers.nfMem t u))
                (quoteTerm s) n
            simp [Formula.substAt]
  | himp ihp ihq => simp [Formula.substAt, ihp, ihq]
  | hall ih => simp [Formula.substAt, ih (n := n + 1)]

@[simp] theorem quoteFormula_neg (p : Fol.formula SourceLNF) :
    quoteFormula (Fol.not' p) = Formula.neg (quoteFormula p) := rfl

/-! ## Structural translation of all eight Flypitch proof constructors -/

theorem quote_image_lift1 (Gamma : Set (Fol.formula SourceLNF)) :
    quoteFormula '' (Fol.lift_formula1 '' Gamma) =
      Formula.lift1 '' (quoteFormula '' Gamma) := by
  ext q
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨quoteFormula p, ⟨p, hp, rfl⟩, ?_⟩
    exact (quoteFormula_liftAt p 1 0).symm
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨Fol.lift_formula1 p, ⟨p, hp, rfl⟩, ?_⟩
    exact quoteFormula_liftAt p 1 0

noncomputable def translatePrf {Gamma : Set (Fol.formula SourceLNF)}
    {p : Fol.formula SourceLNF} (h : Fol.prf Gamma p) :
    NFNotWPP.Prf (quoteFormula '' Gamma) (quoteFormula p) := by
  induction h with
  | axm hmem =>
      exact .axm (Set.mem_image_of_mem quoteFormula hmem)
  | impI _ ih =>
      apply NFNotWPP.Prf.impI
      simpa only [Set.image_insert_eq] using ih
  | impE A _ _ ihpq ihp =>
      exact NFNotWPP.Prf.impE (quoteFormula A) ihpq ihp
  | falsumE _ ih =>
      apply NFNotWPP.Prf.falsumE
      simpa only [Set.image_insert_eq, quoteFormula_neg] using ih
  | allI _ ih =>
      apply NFNotWPP.Prf.allI
      rw [← quote_image_lift1]
      exact ih
  | allE₂ A t _ ih =>
      simpa only [quoteFormula_all, quoteFormula_subst] using
        (NFNotWPP.Prf.allE₂ (quoteFormula A) (quoteTerm t) ih)
  | ref Gamma t =>
      exact NFNotWPP.Prf.ref (quoteFormula '' Gamma) (quoteTerm t)
  | subst₂ s t f _ _ ihst ihf =>
      rw [quoteFormula_subst]
      apply NFNotWPP.Prf.subst₂ (quoteTerm s) (quoteTerm t) (quoteFormula f)
      · exact ihst
      · rw [← quoteFormula_subst]
        exact ihf

/-! ## Reuse of the independently checked finite-theory and nominal bridges -/

theorem quoteFormula_eq_sourceEquality :
    quoteFormula = NFNotWPP.SourceEquality.quoteFormula := by
  rfl

theorem quoteFormula_eq_theoryBridge :
    quoteFormula = NFNotWPP.TheoryBridgeProbe.quoteFormula := by
  rfl

theorem quote_sourceTheory :
    quoteFormula ''
        NFChoice.Foundation.ExactLiteralTrial.LiteralHailperinNF.fst =
      NFNotWPP.LiteralHailperinNF := by
  rw [quoteFormula_eq_theoryBridge]
  exact NFNotWPP.TheoryBridgeProbe.quote_sourceTheory

theorem quote_NF :
    quoteFormula '' NFChoice.Foundation.NF.fst = NFNotWPP.NF := by
  rw [quoteFormula_eq_theoryBridge]
  exact NFNotWPP.TheoryBridgeProbe.quote_NF

theorem quote_accepted_sourceWPP :
    quoteFormula
        (NFChoice.DirectNominalPrf.Nominal.lowerWff id
          NFChoice.Compiler.CompactSourceSyntax.syn_wwpp) =
      NFNotWPP.SourceWPPFOL := by
  rw [quoteFormula_eq_sourceEquality]
  exact NFNotWPP.SourceEquality.quote_accepted_sourceWPP

theorem quote_accepted_not_sourceWPP :
    quoteFormula
        (NFChoice.DirectNominalPrf.Nominal.lowerWff id
          (NFChoice.SemanticCore.Wff.neg
            NFChoice.Compiler.CompactSourceSyntax.syn_wwpp)) =
      Formula.neg NFNotWPP.SourceWPPFOL := by
  rw [quoteFormula_eq_sourceEquality]
  calc
    NFNotWPP.SourceEquality.quoteFormula
        (NFChoice.DirectNominalPrf.Nominal.lowerWff id
          (NFChoice.SemanticCore.Wff.neg
            NFChoice.Compiler.CompactSourceSyntax.syn_wwpp)) =
        NFNotWPP.Nominal.lowerWff id
          (NFNotWPP.SourceEquality.reflectWff
            (NFChoice.SemanticCore.Wff.neg
              NFChoice.Compiler.CompactSourceSyntax.syn_wwpp)) :=
      NFNotWPP.SourceEquality.quote_lowerWff id _
    _ = Formula.neg NFNotWPP.SourceWPPFOL := by
      rw [NFNotWPP.SourceEquality.reflectWff_neg,
        NFNotWPP.SourceEquality.reflect_sourceWPP]
      rfl

end SolutionBridge

theorem NF_proves_not_WPP :
    NF ⊢ₛ' Formula.neg SourceWPPFOL := by
  have translated := SolutionBridge.translatePrf
    NFChoice.Foundation.NFStandard.nfPrfNotSourceWPP
  rw [SolutionBridge.quote_NF] at translated
  rw [SolutionBridge.quote_accepted_not_sourceWPP] at translated
  exact ⟨translated⟩

#print axioms NF_proves_not_WPP

end NFNotWPP
