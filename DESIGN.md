# Literal Hailperin NF derives not-WPP: Palomar challenge design

## Delivered statement

`Challenge.lean` is a self-contained challenge file. It imports only Mathlib,
defines a membership-only first-order syntax and proof calculus, spells out the
eleven literal Hailperin axioms, transparently expands the exact Metamath source
formula `wwpp`, and ends with one deliberate proof hole:

```lean
theorem NFNotWPP.hailperinNF_proves_not_WPP :
    NFNotWPP.LiteralHailperinNF ⊢ₛ'
      NFNotWPP.Formula.neg NFNotWPP.SourceWPPFOL
```

The current file is 777 physical lines and 32,621 bytes, below the
1,000-line and 100-KiB limits. Its SHA-256 is
`C11A4D460ECA22BE99ACF19557BD63D15B43A17EF3596982E096B3680C303CA1`.

It compiles successfully with Lean 4.30.0-rc2. The only warning is the expected
warning for the final `sorry`.

## What is exact and what is merely a presentation change

The mathematical object is the same one used by the accepted C18 endpoint:

- The theory is the range of the exact eleven source axioms `ax-ext`, `ax-nin`,
  `ax-xp`, `ax-cnv`, `ax-1c`, `ax-sset`, `ax-si`, `ax-ins2`, `ax-ins3`,
  `ax-typlower`, and `ax-sn`.
- Constructor-bearing class expressions in those axioms are eliminated
  extensionally. In particular, nested class singletons and class ordered pairs
  are not replaced by assertions that corresponding sets exist.
- `wwpp` is the exact compact source expansion. Its ordered pair is the NF
  source pair `syn_cop`, built through `syn_cphi`; it is not silently replaced
  by the ordinary Kuratowski pair `syn_copk`.
- The proof calculus has exactly the eight primitive constructors of
  `Flypitch4.Fol.prf`: hypothesis, implication introduction, implication
  elimination, classical falsum elimination, universal introduction,
  universal elimination, equality reflexivity, and equality substitution.
  Lifting and substitution use Flypitch's de Bruijn conventions.

There are two intentional presentation changes:

1. Membership is a primitive `Formula.mem x y` node. Flypitch represents that
   atom as two `apprel` nodes over its sole binary relation symbol. This is a
   lossless one-to-one compression in the function-free language.
2. Closed, intrinsically scoped axiom data are erased to the raw `Nat`-indexed
   formula syntax before entering the proof calculus. The erased indices are
   exactly the `.fst` formulas used by `Fol.SentTheory.fst`.

Thus the challenge theorem is not definitionally the same Lean type as the
Flypitch theorem, because it deliberately does not import Flypitch. It is the
image of that theorem under a small structural isomorphism.

## Why the target uses `id`

The target is defined by

```lean
def SourceWPPFOL : Formula := Nominal.lowerWff id Source.syn_wwpp
```

This is deliberate. The accepted endpoint has type

```lean
Nominal.NPrf (.neg syn_wwpp)
```

and `NPrf p` is `∀ rho, Fol.prf ... (Nominal.lowerWff rho p)`. Therefore its
proof can be instantiated directly at `id`. No semantic completeness wrapper,
noncomputable closed-formula totalizer, or comparison with
`WPPCompactEndpoint.SourceWPPSentence` is needed.

The exact source term is closed. `Challenge.lean` contains the kernel-reduction
certificate

```lean
theorem SourceWPP_closed : Source.syn_wwpp.fv = ∅ := by
  set_option maxRecDepth 100000 in
    rfl
```

Hence the initial environment has no mathematical effect; `id` and a constant
zero environment are equally valid. `id` was chosen because it makes the
reference-solution instantiation literal and introduces no extra definition.

The closedness proof does not use `native_decide`. Its axiom report is exactly
`propext`, `Classical.choice`, and `Quot.sound`, the same standard trio allowed
by the accepted endpoint.

## Exact-name contract

A Palomar/NanoDa package and its validator should treat the following as the
public contract:

1. The challenge file is named `Challenge.lean`.
2. The required declaration has the fully qualified name
   `NFNotWPP.hailperinNF_proves_not_WPP`.
3. The expected type is exactly the elaborated type printed above. An alias,
   an implication from a new hypothesis, or a theorem in another namespace is
   not a successful submission.
4. The declarations defining `Formula`, `Prf`, `LiteralHailperinNF`,
   `Source.syn_wwpp`, `Nominal.lowerWff`, and `SourceWPPFOL` are part of the
   frozen statement prefix. A robust validator should hash or otherwise freeze
   that prefix and permit changes only to the final proof body.
5. A submitted solution must contain no `sorry`, `admit`, new `axiom`, new
   `opaque` assumption, or unsafe proof escape. The normal Lean/Mathlib kernel
   axioms may remain.

Name equality alone is insufficient: Lean permits shadowing or restating a
similar theorem against altered definitions. Freezing the prefix and checking
the fully qualified declaration type prevents that failure mode.

## Comparator/isomorphism contract

For independent comparison with the existing Flypitch development, the
reference comparator should implement these equations.

### Formula map

For function-free Flypitch terms, map `&k` to `k`. Then map:

```text
Fol.preformula.falsum                         ↦ Formula.falsum
Fol.preformula.equal (&x) (&y)               ↦ Formula.equal x y
apprel (apprel (rel LNFRelation.mem) (&x))
       (&y)                                   ↦ Formula.mem x y
Fol.preformula.imp p q                       ↦ Formula.imp (map p) (map q)
Fol.preformula.all p                         ↦ Formula.all (map p)
```

Any function symbol, partial relation application, or non-membership relation
is impossible in the intended source and should make the comparator fail.

### Theory map

For every `name : HailperinAxiomName`, the comparator must establish

```text
map ((ExactLiteralTrial.literalAxiomFormula name).fst)
  = NFNotWPP.literalAxiomFormula (mapName name).
```

Consequently the image of `LiteralHailperinNF.fst` is exactly
`NFNotWPP.LiteralHailperinNF`; subset in only one direction is not enough.

### Source/lowering map

Translate the two constructors of the original nominal `Class` and all seven
constructors of nominal `Wff` homomorphically. The required endpoint equation
is

```text
map (DirectNominalPrf.Nominal.lowerWff id
       CompactSourceSyntax.syn_wwpp)
  = NFNotWPP.SourceWPPFOL.
```

The copied `syn_wwpp` nominal AST has already been compared against the
accepted `WPPCompactSourceSyntax.syn_wwpp` after this constructor translation;
the comparison passed. The remaining lowering equality is best proved
compositionally in the reference solution rather than by normalizing both
very large formulas in one native-decision call.

### Proof map

Recursively translate each `Fol.prf` constructor to the correspondingly named
`NFNotWPP.Prf` constructor. The only supporting lemmas required are that the
formula map commutes with:

- `Fol.lift_formula1`, including the image of a hypothesis set;
- `Fol.subst_formula` for variable terms;
- insertion and image of theories.

No mathematical theorem about NF or WPP occurs in this bridge. It is a
structural recursor plus de Bruijn bookkeeping.

## Minimal reference-solution route

The intended internal reference solution is:

1. Import the accepted C18 endpoint
   `g_wppfiniteblocknotwppndv : Nominal.NPrf (.neg syn_wwpp)`.
2. Instantiate it at `rho := id`.
3. Translate the resulting `Fol.prf` by structural recursion into
   `NFNotWPP.Prf`.
4. Rewrite the mapped theory and mapped conclusion with the comparator lemmas.
5. Wrap the proof term in `Nonempty.intro`.

This route deliberately bypasses the semantic final wrapper. It should be a
small adapter, not another replay of the 4,321-theorem Metamath closure.

## Audited source anchors

The challenge was derived from these pinned sources:

- `Flypitch4/Fol.lean`:
  `D10D42D54568C822C593A4CE0C3341EA438F0A30C7CF98D91439276F42F44251`
- `NFChoiceExactLiteral.lean`:
  `1E98C0E0B9BA90B9501A7160DFE27D836B86E78698F00C1D9DB43160FC83574A`
- `NominalWffPrf.lean`:
  `987B1BDE1815040729F21006FF8D52F63AA7975B3ED3516B2F3A51CDA44F9979`
- `CompactSourceSyntax.lean`:
  `0EB8A4D1E7919925D60BCA88CC5663D1CC6ACFDC4B65DE8DA37D6906F71D02F8`
- `WPPCompactSourceSyntax.lean`:
  `EED1484C89AF7BA7186B2D022C4D6BE5CB1156EA07B9423CD22D6D714A219CE1`

These hashes are provenance anchors, not runtime dependencies of the
self-contained challenge.
