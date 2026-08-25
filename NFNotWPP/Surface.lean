import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Basic

/-!
# Shared proof-free statement surface for NF refutes WPP

This module contains every transparent constructor used by the Palomar
Challenge and Solution, through the exact standard-NF theory and exact WPP
formula. It deliberately contains no proof of the headline theorem and imports
no solution-side proof module. Compiling this surface once ensures that
Comparator sees exactly the same declarations on both sides.
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

/-! ## Standard NF: extensionality and stratified comprehension -/

namespace Formula

/-- Apply universal quantification `n` times. -/
def alls : Nat -> Formula -> Formula
  | 0, p => p
  | n + 1, p => .all (alls n p)

end Formula

namespace BFormula

/-- An integer type assignment certifies the ordinary NF stratification rules. -/
def StratifiedBy {n : Nat} (ty : Fin n -> Int) : BFormula n -> Prop
  | .falsum => True
  | .equal x y => ty x = ty y
  | .mem x y => ty y = ty x + 1
  | .imp p q => StratifiedBy ty p ∧ StratifiedBy ty q
  | .all p => ∃ k : Int, StratifiedBy (Fin.cases k ty) p

/-- A formula is stratified when it admits an integer type assignment. -/
def Stratified {n : Nat} (p : BFormula n) : Prop :=
  ∃ ty : Fin n -> Int, StratifiedBy ty p

/-- Universally close every free de Bruijn variable. -/
def closeAll {n : Nat} (p : BFormula n) : Formula :=
  Formula.alls n (erase p)

end BFormula

/-- The open assertion that a set has exactly the extension selected by `p`. -/
def comprehensionBody {n : Nat} (p : BFormula (n + 1)) : BFormula n :=
  BFormula.ex (BFormula.eqCandidateToPredicate p)

/-- The universally closed comprehension axiom associated with `p`. -/
def comprehensionInstance {n : Nat} (p : BFormula (n + 1)) : Formula :=
  BFormula.closeAll (comprehensionBody p)

/-- Every stratified instance of the comprehension schema. -/
def StratifiedComprehension : SentTheory :=
  {f | ∃ (n : Nat) (p : BFormula (n + 1)),
    BFormula.Stratified p ∧ f = comprehensionInstance p}

/-- Standard NF: extensionality plus the full stratified-comprehension schema. -/
abbrev NF : SentTheory :=
  insert (BFormula.erase literalAxExt) StratifiedComprehension

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

end NFNotWPP

