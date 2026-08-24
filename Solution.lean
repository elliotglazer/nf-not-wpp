import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Basic
import NominalWPPReplayChunk018Compact001

/-!
# Proved solution: literal Hailperin NF derives the negation of WPP

This module independently repeats the transparent Challenge declarations and
then imports the accepted proof only through its solution-side dependency. WPP
means the **Weak Partition Principle**: if there are a surjection from `y` onto
`x` and an injection from `y` into `x`, then there is an injection from `x`
into `y`. The final proof instantiates the accepted C18
nominal endpoint at the identity environment and translates all eight
first-order proof constructors structurally.
-/

namespace NFNotWPP

/-! ## A membership-only first-order syntax and Flypitch's eight proof rules -/

/--
Unscoped first-order formulas in the function-free language with equality and
membership. Natural numbers are de Bruijn variable indices; `all p` binds index
zero in `p`.
-/
inductive Formula where
  | falsum : Formula
  | equal : Nat -> Nat -> Formula
  | mem : Nat -> Nat -> Formula
  | imp : Formula -> Formula -> Formula
  | all : Formula -> Formula
  deriving DecidableEq, Repr

namespace Formula

/-- Object-language negation, encoded as implication to falsity. -/
def neg (p : Formula) : Formula := .imp p .falsum
/-- Object-language conjunction, encoded from implication and negation. -/
def conj (p q : Formula) : Formula := neg (.imp p (neg q))
/-- Object-language disjunction, encoded as `not p -> q`. -/
def disj (p q : Formula) : Formula := .imp (neg p) q
/-- Object-language biconditional: both implications hold. -/
def biimp (p q : Formula) : Formula := conj (.imp p q) (.imp q p)
/-- Object-language existential quantification, encoded by classical duality. -/
def ex (p : Formula) : Formula := neg (.all (neg p))

/-- Flypitch's `lift_term_at`, specialized to the function-free language. -/
def liftTermAt (k n m : Nat) : Nat := if m <= k then k + n else k

/-- Flypitch's `lift_formula_at`, with membership made a primitive atom. -/
def liftAt : Formula -> Nat -> Nat -> Formula
  | .falsum, _, _ => .falsum
  | .equal x y, n, m => .equal (liftTermAt x n m) (liftTermAt y n m)
  | .mem x y, n, m => .mem (liftTermAt x n m) (liftTermAt y n m)
  | .imp p q, n, m => .imp (liftAt p n m) (liftAt q n m)
  | .all p, n, m => .all (liftAt p n (m + 1))

/-- Shift every free de Bruijn index by one. -/
def lift1 (p : Formula) : Formula := liftAt p 1 0

/-- Flypitch's `subst_term`, specialized to variables as the only terms. -/
def substTerm (k s n : Nat) : Nat :=
  if k < n then k else if n < k then k - 1 else liftTermAt s n 0

/-- Flypitch's `subst_formula`. -/
def substAt : Formula -> Nat -> Nat -> Formula
  | .falsum, _, _ => .falsum
  | .equal x y, s, n => .equal (substTerm x s n) (substTerm y s n)
  | .mem x y, s, n => .mem (substTerm x s n) (substTerm y s n)
  | .imp p q, s, n => .imp (substAt p s n) (substAt q s n)
  | .all p, s, n => .all (substAt p s (n + 1))

end Formula

/-- The eight constructors of `Flypitch4.Fol.prf`, specialized to LNF. -/
inductive Prf : Set Formula -> Formula -> Type
  | axm {Gamma A} (h : A ∈ Gamma) : Prf Gamma A
  | impI {Gamma : Set Formula} {A B}
      (h : Prf (insert A Gamma) B) : Prf Gamma (.imp A B)
  | impE {Gamma} (A) {B}
      (h₁ : Prf Gamma (.imp A B)) (h₂ : Prf Gamma A) : Prf Gamma B
  | falsumE {Gamma : Set Formula} {A}
      (h : Prf (insert (Formula.neg A) Gamma) .falsum) : Prf Gamma A
  | allI {Gamma A}
      (h : Prf (Formula.lift1 '' Gamma) A) : Prf Gamma (.all A)
  | allE₂ {Gamma} (A) (t : Nat)
      (h : Prf Gamma (.all A)) : Prf Gamma (Formula.substAt A t 0)
  | ref (Gamma) (t : Nat) : Prf Gamma (.equal t t)
  | subst₂ {Gamma} (s t : Nat) (f : Formula)
      (h₁ : Prf Gamma (.equal s t))
      (h₂ : Prf Gamma (Formula.substAt f s 0)) :
      Prf Gamma (Formula.substAt f t 0)

/-- A first-order theory represented as the set of its sentence formulas. -/
abbrev SentTheory := Set Formula
/-- Syntactic derivability: a proof object for `p` from the sentence set `T`. -/
def SProvable (T : SentTheory) (p : Formula) : Prop := Nonempty (Prf T p)
scoped infix:51 " ⊢ₛ' " => SProvable

/-! ## Intrinsically scoped data for the exact eleven Hailperin axioms -/

/-- Intrinsically scoped formulas; the index is the number of variables in scope. -/
inductive BFormula : Nat -> Type
  | falsum : BFormula n
  | equal : Fin n -> Fin n -> BFormula n
  | mem : Fin n -> Fin n -> BFormula n
  | imp : BFormula n -> BFormula n -> BFormula n
  | all : BFormula (n + 1) -> BFormula n

/-- A closed intrinsically scoped formula. -/
abbrev Sentence := BFormula 0

namespace BFormula

/-- Scoped negation, encoded as implication to falsity. -/
def neg {n} (p : BFormula n) : BFormula n := .imp p .falsum
/-- Scoped conjunction, encoded from implication and negation. -/
def conj {n} (p q : BFormula n) : BFormula n := neg (.imp p (neg q))
/-- Scoped disjunction, encoded as `not p -> q`. -/
def disj {n} (p q : BFormula n) : BFormula n := .imp (neg p) q
/-- Scoped biconditional: both implications hold. -/
def biimp {n} (p q : BFormula n) : BFormula n :=
  conj (.imp p q) (.imp q p)
/-- Scoped existential quantification, encoded by classical duality. -/
def ex {n} (p : BFormula (n + 1)) : BFormula n := neg (.all (neg p))

/-- Forget the scope proof while preserving every de Bruijn index. -/
def erase : BFormula n -> Formula
  | .falsum => .falsum
  | .equal x y => .equal x.val y.val
  | .mem x y => .mem x.val y.val
  | .imp p q => .imp (erase p) (erase q)
  | .all p => .all (erase p)

/-- Rename every free variable, extending the renaming beneath binders. -/
def renameVars {n m} (rho : Fin n -> Fin m) : BFormula n -> BFormula m
  | .falsum => .falsum
  | .equal x y => .equal (rho x) (rho y)
  | .mem x y => .mem (rho x) (rho y)
  | .imp p q => .imp (renameVars rho p) (renameVars rho q)
  | .all p => .all (renameVars (Fin.cases 0 (fun i => Fin.succ (rho i))) p)

/-- Add a new candidate variable in front of a unary class predicate. -/
def liftClassPredicate {n} (p : BFormula (n + 1)) : BFormula (n + 2) :=
  renameVars (Fin.cases 0 (fun i => Fin.succ (Fin.succ i))) p

/-- Say that variable zero has exactly the members selected by `p`. -/
def eqCandidateToPredicate {n}
    (p : BFormula (n + 1)) : BFormula (n + 1) :=
  .all (biimp (.mem 0 1) (liftClassPredicate p))

/-- Say that set variable `s` is the singleton of set variable `a`. -/
def singleton {n} (s a : Fin n) : BFormula n :=
  .all (biimp (.mem 0 (Fin.succ s)) (.equal 0 (Fin.succ a)))

/-- The ordinary subset relation between set variables `a` and `b`. -/
def subset {n} (a b : Fin n) : BFormula n :=
  .all (.imp (.mem 0 (Fin.succ a)) (.mem 0 (Fin.succ b)))

/-- Say that `y` is the singleton of some set. -/
def isSomeSingleton {n} (y : Fin n) : BFormula n :=
  ex (singleton (Fin.succ y) 0)

end BFormula

/-- Class terms used only to spell the finite Hailperin axioms literally. -/
inductive LiteralClass : Nat -> Type
  | setVar : Fin n -> LiteralClass n
  | singleton : LiteralClass n -> LiteralClass n
  | unorderedPair : LiteralClass n -> LiteralClass n -> LiteralClass n
  | kPair : LiteralClass n -> LiteralClass n -> LiteralClass n

namespace LiteralClass

/-- The membership predicate of a literal class, with candidate at index zero. -/
def membership : {n : Nat} -> LiteralClass n -> BFormula (n + 1)
  | _, .setVar a => .mem 0 (Fin.succ a)
  | _, .singleton A => BFormula.eqCandidateToPredicate (membership A)
  | _, .unorderedPair A B =>
      BFormula.disj
        (BFormula.eqCandidateToPredicate (membership A))
        (BFormula.eqCandidateToPredicate (membership B))
  | _, .kPair A B =>
      let memA := membership A
      let memB := membership B
      let memSingletonA := BFormula.eqCandidateToPredicate memA
      let memPairAB := BFormula.disj
        (BFormula.eqCandidateToPredicate memA)
        (BFormula.eqCandidateToPredicate memB)
      BFormula.disj
        (BFormula.eqCandidateToPredicate memSingletonA)
        (BFormula.eqCandidateToPredicate memPairAB)

/-- Extensional equality of two literal classes. -/
def classEq {n} (A B : LiteralClass n) : BFormula n :=
  .all (BFormula.biimp (membership A) (membership B))

/-- Say that set variable `x` is extensionally equal to literal class `A`. -/
def setEqClass {n} (x : Fin n) (A : LiteralClass n) : BFormula n :=
  classEq (.setVar x) A

/-- Say that literal class `A` is a set and is a member of set variable `r`. -/
def classMemSet {n} (A : LiteralClass n) (r : Fin n) : BFormula n :=
  BFormula.ex (BFormula.conj
    (BFormula.eqCandidateToPredicate (membership A))
    (.mem 0 (Fin.succ r)))

end LiteralClass

open LiteralClass

/-- Literal assertion that `s` is the singleton of `a`. -/
def literalSingleton {n} (s a : Fin n) : BFormula n :=
  setEqClass s (.singleton (.setVar a))
/-- Literal assertion that `p` is the unordered pair of `a` and `b`. -/
def literalUnorderedPair {n} (p a b : Fin n) : BFormula n :=
  setEqClass p (.unorderedPair (.setVar a) (.setVar b))
/-- Literal assertion that `p` is the Kuratowski ordered pair of `a` and `b`. -/
def literalKPair {n} (p a b : Fin n) : BFormula n :=
  setEqClass p (.kPair (.setVar a) (.setVar b))
/-- Say that the Kuratowski pair of `a` and `b` belongs to `r`. -/
def literalPairMem {n} (a b r : Fin n) : BFormula n :=
  classMemSet (.kPair (.setVar a) (.setVar b)) r
/-- Literal assertion that `d` is the double singleton of `a`. -/
def literalDoubleSingleton {n} (d a : Fin n) : BFormula n :=
  setEqClass d (.singleton (.singleton (.setVar a)))
/-- Say that the pair of the singletons of `a` and `b` belongs to `r`. -/
def literalSingletonPairMem {n} (a b r : Fin n) : BFormula n :=
  classMemSet (.kPair (.singleton (.setVar a)) (.singleton (.setVar b))) r
/-- The literal nested-pair membership pattern used by the insertion axioms. -/
def literalInsertedPairMem {n} (z w t r : Fin n) : BFormula n :=
  classMemSet
    (.kPair (.singleton (.singleton (.setVar z)))
      (.kPair (.setVar w) (.setVar t))) r
/-- Say that the pair of `a` and the singleton of `z` belongs to `r`. -/
def literalPairSingletonSecondMem {n} (a z r : Fin n) : BFormula n :=
  classMemSet (.kPair (.setVar a) (.singleton (.setVar z))) r

/-!
### The eleven object-theory axioms

The Lean names retain the source Metamath labels. Their ordinary readings are:

| Source label | Role in Hailperin's finite presentation |
| --- | --- |
| `ax-ext` | extensionality |
| `ax-nin` | existence of the membership NAND of two sets |
| `ax-xp` | existence of the Kuratowski cross product of the universe with a set |
| `ax-cnv` | existence of the converse of a Kuratowski relation |
| `ax-1c` | existence of the set of all singletons |
| `ax-sset` | existence of the Kuratowski relation representing subset |
| `ax-si` | singleton-image/type-raising of a relation |
| `ax-ins2`, `ax-ins3` | insertion of a variable in the second or third relation coordinate |
| `ax-typlower` | Hailperin's type-lowering (`P6`) operation |
| `ax-sn` | existence of each singleton |

The formulas immediately below are the literal membership/equality expansions,
with all binders represented intrinsically so ill-scoped indices cannot occur.
-/

def literalAxExt : Sentence :=
  .all (.all (.imp
    (.all (BFormula.biimp (.mem 0 2) (.mem 0 1))) (.equal 1 0)))

def literalAxNin : Sentence :=
  .all (.all (BFormula.ex (.all
    (BFormula.biimp (.mem 0 1)
      (BFormula.neg (BFormula.conj (.mem 0 3) (.mem 0 2)))))))

def literalAxXp : Sentence :=
  .all (BFormula.ex (.all
    (BFormula.biimp (.mem 0 1)
      (BFormula.ex (BFormula.ex
        (BFormula.conj (literalKPair 2 1 0) (.mem 0 4)))))))

def literalAxCnv : Sentence :=
  .all (BFormula.ex (.all (.all
    (BFormula.biimp (literalPairMem 1 0 2) (literalPairMem 0 1 3)))))

def literalAx1c : Sentence :=
  BFormula.ex (.all
    (BFormula.biimp (.mem 0 1) (BFormula.isSomeSingleton 0)))

def literalAxSset : Sentence :=
  BFormula.ex (.all (.all
    (BFormula.biimp (literalPairMem 1 0 2) (BFormula.subset 1 0))))

def literalAxSi : Sentence :=
  .all (BFormula.ex (.all (.all
    (BFormula.biimp
      (literalSingletonPairMem 1 0 2) (literalPairMem 1 0 3)))))

def literalAxIns2 : Sentence :=
  .all (BFormula.ex (.all (.all (.all
    (BFormula.biimp
      (literalInsertedPairMem 2 1 0 3) (literalPairMem 2 0 4))))))

def literalAxIns3 : Sentence :=
  .all (BFormula.ex (.all (.all (.all
    (BFormula.biimp
      (literalInsertedPairMem 2 1 0 3) (literalPairMem 2 1 4))))))

def literalAxTypeLower : Sentence :=
  .all (BFormula.ex (.all
    (BFormula.biimp (.mem 0 1)
      (.all (literalPairSingletonSecondMem 0 1 3)))))

def literalAxSn : Sentence :=
  .all (BFormula.ex (.all
    (BFormula.biimp (.mem 0 1) (.equal 0 2))))

/-- Names of the eleven sentences in Hailperin's finite NF presentation. -/
inductive HailperinAxiomName
  | axExt | axNin | axXp | axCnv | ax1c | axSset
  | axSi | axIns2 | axIns3 | axTypeLower | axSn
  deriving DecidableEq, Repr

/-- Select the intrinsically scoped sentence belonging to an axiom name. -/
def literalAxiomSyntax : HailperinAxiomName -> Sentence
  | .axExt => literalAxExt
  | .axNin => literalAxNin
  | .axXp => literalAxXp
  | .axCnv => literalAxCnv
  | .ax1c => literalAx1c
  | .axSset => literalAxSset
  | .axSi => literalAxSi
  | .axIns2 => literalAxIns2
  | .axIns3 => literalAxIns3
  | .axTypeLower => literalAxTypeLower
  | .axSn => literalAxSn

/-- Erase intrinsic scope evidence from one literal axiom without changing indices. -/
def literalAxiomFormula (name : HailperinAxiomName) : Formula :=
  BFormula.erase (literalAxiomSyntax name)

/-- The object theory: the range of exactly the eleven named Hailperin formulas. -/
abbrev LiteralHailperinNF : SentTheory := Set.range literalAxiomFormula

/-! ## Exact nominal source syntax and deterministic lowering -/

/-- Named variables in the retained nominal Metamath source syntax. -/
abbrev Var := Nat

/-!
`Class` and `Wff` are the exact nominal source AST used to expand the Metamath
token `WPP`. A class is a variable or an abstraction; a wff has the usual
logical, object equality/membership, and class equality/membership nodes.
-/
mutual
  inductive Class where
    | cv : Var -> Class
    | cab : Var -> Wff -> Class
    deriving DecidableEq, Repr

  inductive Wff where
    | falsum : Wff
    | imp : Wff -> Wff -> Wff
    | all : Var -> Wff -> Wff
    | objEq : Var -> Var -> Wff
    | objMem : Var -> Var -> Wff
    | classEq : Class -> Class -> Wff
    | classMem : Class -> Class -> Wff
    deriving DecidableEq, Repr
end

/-- Nominal object-language negation, encoded as implication to falsity. -/
def Wff.neg (p : Wff) : Wff := .imp p .falsum

mutual
  /-- The finite support of a nominal class term. -/
  def Class.fv : Class -> Finset Var
    | .cv x => {x}
    | .cab x p => p.fv.erase x

  /-- The finite support of a nominal formula. -/
  def Wff.fv : Wff -> Finset Var
    | .falsum => ∅
    | .imp p q => p.fv ∪ q.fv
    | .all x p => p.fv.erase x
    | .objEq x y => {x, y}
    | .objMem x y => {x, y}
    | .classEq A B => A.fv ∪ B.fv
    | .classMem A B => A.fv ∪ B.fv
end

/-- Deterministically choose a name above every member of a finite support. -/
def freshVar (support : Finset Var) (offset : Nat := 0) : Var :=
  support.sup id + offset + 1

namespace Nominal

/-- Shift every de Bruijn index supplied by a nominal environment. -/
def liftRho (rho : Var -> Nat) : Var -> Nat := fun x => rho x + 1
/-- Extend an environment beneath a binder for named variable `x`. -/
def bindRho (rho : Var -> Nat) (x : Var) : Var -> Nat :=
  fun y => if y = x then 0 else rho y + 1
/-- Override the de Bruijn index assigned to one named variable. -/
def updateRho (rho : Var -> Nat) (x value : Var) : Var -> Nat :=
  fun y => if y = x then value else rho y

/-!
Lowering interprets named variables as de Bruijn indices. Class equality is
extensional equality of membership predicates; class membership introduces a
witness set extensionally equal to the left class and belonging to the right.
-/
mutual
  def lowerClassPred (rho : Var -> Nat) (candidate : Nat) : Class -> Formula
    | .cv x => .mem candidate (rho x)
    | .cab x p => lowerWff (updateRho rho x candidate) p

  def lowerWff (rho : Var -> Nat) : Wff -> Formula
    | .falsum => .falsum
    | .imp p q => .imp (lowerWff rho p) (lowerWff rho q)
    | .all x p => .all (lowerWff (bindRho rho x) p)
    | .objEq x y => .equal (rho x) (rho y)
    | .objMem x y => .mem (rho x) (rho y)
    | .classEq A B =>
        .all (Formula.biimp
          (lowerClassPred (liftRho rho) 0 A)
          (lowerClassPred (liftRho rho) 0 B))
    | .classMem A B =>
        Formula.ex (Formula.conj
          (.all (Formula.biimp (.mem 0 1)
            (lowerClassPred (liftRho (liftRho rho)) 0 A)))
          (lowerClassPred (liftRho rho) 0 B))
end

end Nominal

/-!
## Reading the exact Metamath source expansion

Every `syn_*` definition below is a transparent transliteration of the source
constructor with the same name (minus the prefix). The initial letter follows
Metamath convention: `w` constructs a formula and `c` constructs a class.
These groups provide an audit map without replacing the literal definitions:

| Constructors | Ordinary meaning |
| --- | --- |
| `wtru`, `wb`, `wo`, `wa`, `w3o`, `w3a`, `wnan`, `wex`, `wnf`, `wsb`, `weu`, `wmo` | truth, biconditional, disjunction, conjunction, ternary variants, NAND, existential, freshness, substitution, unique existence, and at-most-one |
| `wnfc`, `wne`, `wral`, `wrex`, `wreu`, `wrmo`, `crab`, `wsbc`, `csb` | class non-freeness/inequality, class-bounded quantifiers, class abstraction, and substitution |
| `cvv`, `c0`, `cnin`, `ccompl`, `cin`, `cun`, `cdif`, `csymdif`, `cif`, `wss`, `wpss` | universal/empty classes, Boolean class operations and conditional, subset, and proper subset |
| `cpw`, `csn`, `cpr`, `ctp`, `cuni`, `cint`, `ciun` | power class, singleton, unordered pair/triple, union, intersection, and indexed union |
| `copk`, `cxpk`, `ccnvk`, `cins2k`, `cins3k`, `cimak`, `ccomk`, `cp6`, `csik`, `cssetk`, `cimagek`, `cidk` | Kuratowski-pair relation algebra and the Hailperin operators guaranteed by the finite axioms |
| `c1c`, `cpw1`, `cuni1`, `cio`, `c0c`, `cplc`, `cnnc`, `cfin`, `clefin`, `cltfin`, `cncfin`, `ctfin`, `cevenfin`, `coddfin`, `wsfin`, `cspfin`, `cphi` | exact finite-cardinal/parity machinery defining the NF type-raising map `Phi` |
| `cop`, `copab` | the source's Quine--Rosser ordered pair and ordered-pair abstraction (not the Kuratowski pair `copk`) |
| `wbr`, `ccom`, `cima`, `cid`, `ccnv`, `crn`, `cdm` | relation application, composition, image, identity, converse, range, and domain |
| `wfun`, `wfn`, `wf`, `wf1`, `wfo` | functional, function-with-domain, function into, one-to-one, and onto predicates |

Finally, `syn_wwpp` is the literal `df-wpp` body:
`forall x y, ((exists f, f : y -onto-> x) and
(exists g, g : y -1-1-> x)) -> (exists h, h : x -1-1-> y)`.
-/

namespace Source

def syn_wtru : Wff := .imp .falsum .falsum
def syn_wb (ph ps : Wff) : Wff :=
  .neg (.imp (.imp ph ps) (.neg (.imp ps ph)))
def syn_wo (ph ps : Wff) : Wff := .imp (.neg ph) ps
def syn_wa (ph ps : Wff) : Wff := .neg (.imp ph (.neg ps))
def syn_w3o (ph ps ch : Wff) : Wff := syn_wo (syn_wo ph ps) ch
def syn_w3a (ph ps ch : Wff) : Wff := syn_wa (syn_wa ph ps) ch
def syn_wnan (ph ps : Wff) : Wff := .neg (syn_wa ph ps)
def syn_wex (x : Var) (ph : Wff) : Wff := .neg (.all x (.neg ph))
def syn_wnf (x : Var) (ph : Wff) : Wff := .all x (.imp ph (.all x ph))
def syn_wsb (y x : Var) (ph : Wff) : Wff :=
  syn_wa (.imp (.objEq x y) ph) (syn_wex x (syn_wa (.objEq x y) ph))
def syn_weu (x : Var) (ph : Wff) : Wff :=
  let y := freshVar (({x} : Finset Var) ∪ ph.fv) 0
  syn_wex y (.all x (syn_wb ph (.objEq x y)))
def syn_wmo (x : Var) (ph : Wff) : Wff := .imp (syn_wex x ph) (syn_weu x ph)
def syn_wnfc (x : Var) (A : Class) : Wff :=
  let y := freshVar (({x} : Finset Var) ∪ A.fv) 0
  .all y (syn_wnf x (.classMem (.cv y) A))
def syn_wne (A B : Class) : Wff := .neg (.classEq A B)
def syn_wral (x : Var) (A : Class) (ph : Wff) : Wff :=
  .all x (.imp (.classMem (.cv x) A) ph)
def syn_wrex (x : Var) (A : Class) (ph : Wff) : Wff :=
  syn_wex x (syn_wa (.classMem (.cv x) A) ph)
def syn_wreu (x : Var) (A : Class) (ph : Wff) : Wff :=
  syn_weu x (syn_wa (.classMem (.cv x) A) ph)
def syn_wrmo (x : Var) (A : Class) (ph : Wff) : Wff :=
  syn_wmo x (syn_wa (.classMem (.cv x) A) ph)
def syn_crab (x : Var) (A : Class) (ph : Wff) : Class :=
  .cab x (syn_wa (.classMem (.cv x) A) ph)
def syn_cvv : Class :=
  let x := freshVar (∅ : Finset Var) 0
  .cab x (.objEq x x)
def syn_wsbc (A : Class) (x : Var) (ph : Wff) : Wff := .classMem A (.cab x ph)
def syn_csb (A : Class) (x : Var) (B : Class) : Class :=
  let y := freshVar (A.fv ∪ ({x} : Finset Var) ∪ B.fv) 0
  .cab y (syn_wsbc A x (.classMem (.cv y) B))
def syn_cnin (A B : Class) : Class :=
  let x := freshVar (A.fv ∪ B.fv) 0
  .cab x (syn_wnan (.classMem (.cv x) A) (.classMem (.cv x) B))
def syn_ccompl (A : Class) : Class := syn_cnin A A
def syn_cin (A B : Class) : Class := syn_ccompl (syn_cnin A B)
def syn_cun (A B : Class) : Class := syn_cnin (syn_ccompl A) (syn_ccompl B)
def syn_cdif (A B : Class) : Class := syn_cin A (syn_ccompl B)
def syn_csymdif (A B : Class) : Class := syn_cun (syn_cdif A B) (syn_cdif B A)
def syn_wss (A B : Class) : Wff := .classEq (syn_cin A B) A
def syn_wpss (A B : Class) : Wff := syn_wa (syn_wss A B) (syn_wne A B)
def syn_c0 : Class := syn_cdif syn_cvv syn_cvv
def syn_cif (ph : Wff) (A B : Class) : Class :=
  let x := freshVar (ph.fv ∪ A.fv ∪ B.fv) 0
  .cab x (syn_wo (syn_wa (.classMem (.cv x) A) ph)
    (syn_wa (.classMem (.cv x) B) (.neg ph)))
def syn_cpw (A : Class) : Class :=
  let x := freshVar A.fv 0
  .cab x (syn_wss (.cv x) A)
def syn_csn (A : Class) : Class :=
  let x := freshVar A.fv 0
  .cab x (.classEq (.cv x) A)
def syn_cpr (A B : Class) : Class := syn_cun (syn_csn A) (syn_csn B)
def syn_ctp (A B C : Class) : Class := syn_cun (syn_cpr A B) (syn_csn C)
def syn_cuni (A : Class) : Class :=
  let x := freshVar A.fv 0
  let y := freshVar A.fv 1
  .cab x (syn_wex y (syn_wa (.objMem x y) (.classMem (.cv y) A)))
def syn_cint (A : Class) : Class :=
  let x := freshVar A.fv 0
  let y := freshVar A.fv 1
  .cab x (.all y (.imp (.classMem (.cv y) A) (.objMem x y)))
def syn_ciun (x : Var) (A B : Class) : Class :=
  let y := freshVar (({x} : Finset Var) ∪ A.fv ∪ B.fv) 0
  .cab y (syn_wrex x A (.classMem (.cv y) B))
def syn_copk (A B : Class) : Class := syn_cpr (syn_csn A) (syn_cpr A B)
def syn_c1c : Class :=
  let x := freshVar (∅ : Finset Var) 0
  let y := freshVar (∅ : Finset Var) 1
  .cab x (syn_wex y (.classEq (.cv x) (syn_csn (.cv y))))
def syn_cpw1 (A : Class) : Class := syn_cin (syn_cpw A) syn_c1c
def syn_cuni1 (A : Class) : Class := syn_cuni (syn_cin A syn_c1c)

def syn_cxpk (A B : Class) : Class :=
  let x := freshVar (A.fv ∪ B.fv) 0
  let y := freshVar (A.fv ∪ B.fv) 1
  let z := freshVar (A.fv ∪ B.fv) 2
  .cab x (syn_wex y (syn_wex z
    (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
      (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)))))
def syn_ccnvk (A : Class) : Class :=
  let x := freshVar A.fv 0
  let y := freshVar A.fv 1
  let z := freshVar A.fv 2
  .cab x (syn_wex y (syn_wex z
    (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
      (.classMem (syn_copk (.cv z) (.cv y)) A))))
def syn_cins2k (A : Class) : Class :=
  let t := freshVar A.fv 0
  let u := freshVar A.fv 1
  let v := freshVar A.fv 2
  let x := freshVar A.fv 3
  let y := freshVar A.fv 4
  let z := freshVar A.fv 5
  .cab x (syn_wex y (syn_wex z
    (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
      (syn_wex t (syn_wex u (syn_wex v
        (syn_w3a
          (.classEq (.cv y) (syn_csn (syn_csn (.cv t))))
          (.classEq (.cv z) (syn_copk (.cv u) (.cv v)))
          (.classMem (syn_copk (.cv t) (.cv v)) A))))))))
def syn_cins3k (A : Class) : Class :=
  let t := freshVar A.fv 0
  let u := freshVar A.fv 1
  let v := freshVar A.fv 2
  let x := freshVar A.fv 3
  let y := freshVar A.fv 4
  let z := freshVar A.fv 5
  .cab x (syn_wex y (syn_wex z
    (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
      (syn_wex t (syn_wex u (syn_wex v
        (syn_w3a
          (.classEq (.cv y) (syn_csn (syn_csn (.cv t))))
          (.classEq (.cv z) (syn_copk (.cv u) (.cv v)))
          (.classMem (syn_copk (.cv t) (.cv u)) A))))))))
def syn_cimak (A B : Class) : Class :=
  let x := freshVar (A.fv ∪ B.fv) 0
  let y := freshVar (A.fv ∪ B.fv) 1
  .cab x (syn_wrex y B (.classMem (syn_copk (.cv y) (.cv x)) A))
def syn_ccomk (A B : Class) : Class :=
  syn_cimak (syn_cin (syn_cins2k A) (syn_cins3k (syn_ccnvk B))) syn_cvv
def syn_cp6 (A : Class) : Class :=
  let x := freshVar A.fv 0
  .cab x (syn_wss (syn_cxpk syn_cvv (syn_csn (syn_csn (.cv x)))) A)
def syn_csik (A : Class) : Class :=
  let t := freshVar A.fv 0
  let u := freshVar A.fv 1
  let x := freshVar A.fv 2
  let y := freshVar A.fv 3
  let z := freshVar A.fv 4
  .cab x (syn_wex y (syn_wex z
    (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
      (syn_wex t (syn_wex u
        (syn_w3a
          (.classEq (.cv y) (syn_csn (.cv t)))
          (.classEq (.cv z) (syn_csn (.cv u)))
          (.classMem (syn_copk (.cv t) (.cv u)) A)))))))
def syn_cssetk : Class :=
  let x := freshVar (∅ : Finset Var) 0
  let y := freshVar (∅ : Finset Var) 1
  let z := freshVar (∅ : Finset Var) 2
  .cab x (syn_wex y (syn_wex z
    (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
      (syn_wss (.cv y) (.cv z)))))
def syn_cimagek (A : Class) : Class :=
  syn_cdif (syn_cxpk syn_cvv syn_cvv)
    (syn_cimak
      (syn_csymdif (syn_cins2k syn_cssetk)
        (syn_cins3k (syn_ccomk syn_cssetk (syn_ccnvk (syn_csik A)))))
      (syn_cpw1 (syn_cpw1 syn_c1c)))
def syn_cidk : Class :=
  let x := freshVar (∅ : Finset Var) 0
  let y := freshVar (∅ : Finset Var) 1
  let z := freshVar (∅ : Finset Var) 2
  .cab x (syn_wex y (syn_wex z
    (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (.objEq y z))))

def syn_cio (x : Var) (ph : Wff) : Class :=
  let y := freshVar (({x} : Finset Var) ∪ ph.fv) 0
  syn_cuni (.cab y (.classEq (.cab x ph) (syn_csn (.cv y))))
def syn_c0c : Class := syn_csn syn_c0
def syn_cplc (A B : Class) : Class :=
  let x := freshVar (A.fv ∪ B.fv) 0
  let y := freshVar (A.fv ∪ B.fv) 1
  let z := freshVar (A.fv ∪ B.fv) 2
  .cab x (syn_wrex y A (syn_wrex z B
    (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) syn_c0)
      (.classEq (.cv x) (syn_cun (.cv y) (.cv z))))))
def syn_cnnc : Class :=
  let b := freshVar (∅ : Finset Var) 0
  let y := freshVar (∅ : Finset Var) 1
  syn_cint (.cab b
    (syn_wa (.classMem syn_c0c (.cv b))
      (syn_wral y (.cv b) (.classMem (syn_cplc (.cv y) syn_c1c) (.cv b)))))
def syn_cfin : Class := syn_cuni syn_cnnc
def syn_clefin : Class :=
  let w := freshVar (∅ : Finset Var) 0
  let x := freshVar (∅ : Finset Var) 1
  let y := freshVar (∅ : Finset Var) 2
  let z := freshVar (∅ : Finset Var) 3
  .cab x (syn_wex y (syn_wex z
    (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
      (syn_wrex w syn_cnnc (.classEq (.cv z) (syn_cplc (.cv y) (.cv w)))))))
def syn_cltfin : Class :=
  let m := freshVar (∅ : Finset Var) 0
  let n := freshVar (∅ : Finset Var) 1
  let p := freshVar (∅ : Finset Var) 2
  let x := freshVar (∅ : Finset Var) 3
  .cab x (syn_wex m (syn_wex n
    (syn_wa (.classEq (.cv x) (syn_copk (.cv m) (.cv n)))
      (syn_wa (syn_wne (.cv m) syn_c0)
        (syn_wrex p syn_cnnc
          (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (.cv p)) syn_c1c)))))))
def syn_cncfin (A : Class) : Class :=
  let x := freshVar A.fv 0
  syn_cio x (syn_wa (.classMem (.cv x) syn_cnnc) (.classMem A (.cv x)))
def syn_ctfin (M : Class) : Class :=
  let a := freshVar M.fv 0
  let n := freshVar M.fv 1
  syn_cif (.classEq M syn_c0) syn_c0
    (syn_cio n (syn_wa (.classMem (.cv n) syn_cnnc)
      (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))))
def syn_cevenfin : Class :=
  let n := freshVar (∅ : Finset Var) 0
  let x := freshVar (∅ : Finset Var) 1
  .cab x (syn_wa
    (syn_wrex n syn_cnnc (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))))
    (syn_wne (.cv x) syn_c0))
def syn_coddfin : Class :=
  let n := freshVar (∅ : Finset Var) 0
  let x := freshVar (∅ : Finset Var) 1
  .cab x (syn_wa
    (syn_wrex n syn_cnnc
      (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) syn_c1c)))
    (syn_wne (.cv x) syn_c0))
def syn_wsfin (M N : Class) : Wff :=
  let a := freshVar (M.fv ∪ N.fv) 0
  syn_w3a (.classMem M syn_cnnc) (.classMem N syn_cnnc)
    (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) M)
      (.classMem (syn_cpw (.cv a)) N)))
def syn_cspfin : Class :=
  let a := freshVar (∅ : Finset Var) 0
  let x := freshVar (∅ : Finset Var) 1
  let z := freshVar (∅ : Finset Var) 2
  syn_cint (.cab a
    (syn_wa (.classMem (syn_cncfin syn_cvv) (.cv a))
      (syn_wral x (.cv a) (.all z
        (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))))
def syn_cphi (A : Class) : Class :=
  let x := freshVar A.fv 0
  let y := freshVar A.fv 1
  .cab y (syn_wrex x A
    (.classEq (.cv y)
      (syn_cif (.classMem (.cv x) syn_cnnc)
        (syn_cplc (.cv x) syn_c1c) (.cv x))))
def syn_cop (A B : Class) : Class :=
  let x := freshVar (A.fv ∪ B.fv) 0
  let y := freshVar (A.fv ∪ B.fv) 1
  syn_cun
    (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y)))))
    (.cab x (syn_wrex y B
      (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn syn_c0c)))))

def syn_copab (x y : Var) (ph : Wff) : Class :=
  let z := freshVar (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ph.fv) 0
  .cab z (syn_wex x (syn_wex y
    (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph)))
def syn_wbr (A R B : Class) : Wff := .classMem (syn_cop A B) R
def syn_ccom (A B : Class) : Class :=
  let x := freshVar (A.fv ∪ B.fv) 0
  let y := freshVar (A.fv ∪ B.fv) 1
  let z := freshVar (A.fv ∪ B.fv) 2
  syn_copab x y (syn_wex z
    (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y))))
def syn_cima (A B : Class) : Class :=
  let x := freshVar (A.fv ∪ B.fv) 0
  let y := freshVar (A.fv ∪ B.fv) 1
  .cab x (syn_wrex y B (syn_wbr (.cv y) A (.cv x)))
def syn_cid : Class :=
  let x := freshVar (∅ : Finset Var) 0
  let y := freshVar (∅ : Finset Var) 1
  syn_copab x y (.objEq x y)
def syn_ccnv (A : Class) : Class :=
  let x := freshVar A.fv 0
  let y := freshVar A.fv 1
  syn_copab x y (syn_wbr (.cv y) A (.cv x))
def syn_crn (A : Class) : Class := syn_cima A syn_cvv
def syn_cdm (A : Class) : Class := syn_crn (syn_ccnv A)
def syn_wfun (A : Class) : Wff := syn_wss (syn_ccom A (syn_ccnv A)) syn_cid
def syn_wfn (A B : Class) : Wff := syn_wa (syn_wfun A) (.classEq (syn_cdm A) B)
def syn_wf (F A B : Class) : Wff := syn_wa (syn_wfn F A) (syn_wss (syn_crn F) B)
def syn_wf1 (F A B : Class) : Wff := syn_wa (syn_wf F A B) (syn_wfun (syn_ccnv F))
def syn_wfo (F A B : Class) : Wff := syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)

/-- Exact compact expansion of the Metamath source token `wwpp`. -/
def syn_wwpp : Wff :=
  let f := freshVar (∅ : Finset Var) 0
  let g := freshVar (∅ : Finset Var) 1
  let h := freshVar (∅ : Finset Var) 2
  let x := freshVar (∅ : Finset Var) 3
  let y := freshVar (∅ : Finset Var) 4
  .all x (.all y (.imp
    (syn_wa
      (syn_wex f (syn_wfo (.cv f) (.cv y) (.cv x)))
      (syn_wex g (syn_wf1 (.cv g) (.cv y) (.cv x))))
    (syn_wex h (syn_wf1 (.cv h) (.cv x) (.cv y)))))

end Source

/-- Reduction-checkable confirmation that the exact source WPP has no free names. -/
theorem SourceWPP_closed : Source.syn_wwpp.fv = ∅ := by
  set_option maxRecDepth 100000 in
    rfl

/--
The same fixed-environment lowering obtained by instantiating C18's
`Nominal.NPrf (.neg syn_wwpp)` at the identity environment.
-/
def SourceWPPFOL : Formula := Nominal.lowerWff id Source.syn_wwpp

/-!
This solution-only section bridges the accepted nominal source syntax and the
independently repeated Challenge mirror. No proof objects or theory equalities
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
Finite theory-identification layer for the Palomar solution. It deliberately
does not use the C18 endpoint: this section only identifies the eleven accepted
source axioms with the eleven Challenge axioms.
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

end TheoryBridgeProbe

/-!
Generic solution-only bridge from the accepted direct nominal C18 endpoint to
the small Challenge calculus. The exact public theorem below instantiates this
structural translator.
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

theorem hailperinNF_proves_not_WPP :
    LiteralHailperinNF ⊢ₛ' Formula.neg SourceWPPFOL := by
  have accepted :=
    NFChoice.DirectNominalPrf.WPPReplay.g_wppfiniteblocknotwppndv id
  have translated := SolutionBridge.translatePrf accepted
  rw [SolutionBridge.quote_sourceTheory] at translated
  rw [SolutionBridge.quote_accepted_not_sourceWPP] at translated
  exact ⟨translated⟩

end NFNotWPP
