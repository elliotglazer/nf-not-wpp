# Standard NF derives not-WPP: Palomar challenge design

## Delivered statement

`NFNotWPP/Surface.lean` is the shared proof-free statement surface. It imports
only Mathlib, defines a membership-only first-order syntax and proof calculus,
defines standard NF as extensionality plus the full stratified-comprehension
schema, and transparently expands the exact Metamath source formula `wwpp`.
`Challenge.lean` imports that surface and ends with one deliberate proof hole:

```lean
theorem NFNotWPP.NF_proves_not_WPP :
    NFNotWPP.NF ⊢ₛ'
      NFNotWPP.Formula.neg NFNotWPP.SourceWPPFOL
```

This is a syntactic derivability theorem. It neither assumes that NF has a
model nor proves a consistency result. In the public statement,

```lean
abbrev NF : SentTheory :=
  insert (BFormula.erase literalAxExt) StratifiedComprehension
```

where `StratifiedComprehension` contains every universally closed
comprehension instance whose open predicate admits an integer stratification
assignment. Thus the theorem's hypotheses are the standard NF axioms, not
Hailperin's eleven sentences.

The current public artifacts are:

| File | Physical lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `Challenge.lean` | 33 | 1,177 | `1EA53EB73A16D79C85BA6CA9C82AF7C68BCF231EA993BC4CA6FF37B51C49B7F1` |
| `NFNotWPP/Surface.lean` | 810 | 33,542 | `FFFE794DF7DA4158FBF2D855875EAD7C33938160D896D0EEC7ED0020E3243BE3` |
| `Solution.lean` | 1,070 | 43,006 | `FD87AAE4BD63AE44C7ECB6A4D50E7C2A03245837D5D900E7498B6DA9FB19CE13` |

The Challenge remains below Palomar's 1,000-line and 100-KiB statement limits.
It builds with only its intended final `sorry`. The larger reference Solution
builds without `sorry`, `admit`, a custom `axiom`, or an opaque assumption.
Its final `#print axioms` report is exactly `propext`, `Classical.choice`, and
`Quot.sound`.

## The role of the eleven Hailperin axioms

The accepted C18 translation ends in the exact token-level theory
`ExactLiteralTrial.LiteralHailperinNF`, the range of the eleven formulas
`ax-ext`, `ax-nin`, `ax-xp`, `ax-cnv`, `ax-1c`, `ax-sset`, `ax-si`, `ax-ins2`,
`ax-ins3`, `ax-typlower`, and `ax-sn`. Those formulas remain visible in the
Challenge so that the internal translation boundary is transparent.

They are not assumptions of `NFNotWPP.NF_proves_not_WPP`. They are an internal
finite-basis bridge:

```text
accepted C18 proof over LiteralHailperinNF
                 │ replace every axiom leaf
                 ▼
          Flypitch derivation over NF
                 │ structural quotation
                 ▼
       public NFNotWPP.NF derivation
```

The repository also already had a finite theory named
`NFChoice.Foundation.HailperinNF`. It uses an older
existential-intermediate presentation, whereas `LiteralHailperinNF` uses the
literal class-expansion frontend required by the translated Metamath proof.
They are not definitionally equal. `HailperinPresentationBridge.lean` proves
that they have the same models and the same deductive consequences.

## Full NF/Hailperin equivalence

The standard-theory layer under `Proof/NFStandard/` proves both model
directions before invoking first-order completeness.

### Standard NF supplies the finite basis

`Basic.lean` defines intrinsic formulas, integer stratification, universal
closure, comprehension instances, and standard `NF`. `ToHailperin.lean` then
uses extensionality and certified stratified-comprehension instances to
interpret every class expression occurring in each of the eleven literal
axioms. Its endpoint is:

```lean
nf_models_literalHailperin :
  Fol.all_realize_sentence S NF →
  Fol.all_realize_sentence S LiteralHailperinNF
```

This is the mathematically short direction: each finite-basis constructor is
realized by a stratified comprehension.

### The finite basis supplies every NF comprehension instance

The reverse direction constructs the primitive operations represented by the
eleven axioms, packages them as a Hailperin model and then as a cylinder
algebra, and runs the generic cylinder compiler. The main layers are
`HailperinModel.lean`, `HailperinAlgebra.lean`, and `CylinderToNF.lean`. Their
composite endpoint is:

```lean
literalHailperin_models_NF :
  Fol.all_realize_sentence S LiteralHailperinNF →
  Fol.all_realize_sentence S NF
```

This proves extensionality and every certified stratified-comprehension
instance in an arbitrary literal-Hailperin model. It does not postulate or
construct an absolute model of NF.

### From model equivalence to deductive equivalence

`Equivalence.lean` combines the two directions and applies the repository's
first-order soundness/completeness interface. It exports:

```lean
theorem models_NF_iff_literalHailperinNF (S : Fol.Structure LNF) :
    Fol.all_realize_sentence S NF ↔
      Fol.all_realize_sentence S LiteralHailperinNF

theorem nf_literalHailperin_deductivelyEquivalent :
    DeductivelyEquivalent NF LiteralHailperinNF

theorem models_NF_iff_HailperinNF (S : Fol.Structure LNF) :
    Fol.all_realize_sentence S NF ↔
      Fol.all_realize_sentence S HailperinNF

theorem nf_hailperin_deductivelyEquivalent :
    DeductivelyEquivalent NF HailperinNF
```

The last theorem is the requested equivalence between standard NF and the
repository's Hailperin presentation. The literal presentation is retained only
because it is the exact theory expected by the accepted translated proof.

## Replacing the C18 axiom leaves

The accepted endpoint is

```lean
NFChoice.DirectNominalPrf.WPPReplay.g_wppfiniteblocknotwppndv :
  Nominal.NPrf (.neg syn_wwpp)
```

Instantiation at `rho := id` gives a concrete `Fol.prf` whose theory is
`LiteralHailperinNF.fst`. `Consequences.lean` uses the proved NF-to-literal
model inclusion and first-order completeness to obtain

```lean
literalAxiom_derivable_in_NF (name : HailperinAxiomName) :
  NF ⊢ₛ' literalAxiomFormula name
```

`NotWPP.lean` supplies the generic proof transformer

```lean
replacePrfAxioms
    (hΓ : ∀ ⦃p⦄, p ∈ Γ → Fol.prf Δ p)
    (hf : Fol.prf Γ f) : Fol.prf Δ f
```

It recursively preserves all eight primitive Flypitch proof constructors and
replaces each hypothesis constructor by the supplied derivation. Implication
and falsum introduction extend the replacement map under inserted
hypotheses; universal introduction lifts replacement proofs under the bound
variable. The resulting exact source proof is

```lean
nfPrfNotSourceWPP :
  Fol.prf NF.fst (Nominal.lowerWff id (Wff.neg syn_wwpp))
```

Thus the large C18 proof is not replayed a second time and no semantic wrapper
is inserted at the public boundary. Only its eleven axiom leaves are replaced.

## Structural quotation into the public calculus

`Solution.lean` imports the same compiled statement surface as Challenge and
then quotes the Flypitch derivation constructor for constructor.

### Formula and proof maps

For function-free Flypitch terms, `&k` maps to `k`. Formulas map as follows:

```text
Fol.preformula.falsum                         ↦ Formula.falsum
Fol.preformula.equal (&x) (&y)               ↦ Formula.equal x y
apprel (apprel (rel LNFRelation.mem) (&x))
       (&y)                                   ↦ Formula.mem x y
Fol.preformula.imp p q                       ↦ Formula.imp (map p) (map q)
Fol.preformula.all p                         ↦ Formula.all (map p)
```

The proof map handles exactly the eight `Fol.prf` constructors: hypothesis,
implication introduction and elimination, classical falsum elimination,
universal introduction and elimination, equality reflexivity, and equality
substitution. Supporting lemmas show that quotation commutes with lifting,
substitution, insertion, and theory image.

### Exact standard-NF theory map

The earlier literal-basis map remains available, but it is not enough for the
public theorem. The Solution additionally quotes intrinsic formulas, proves
that quotation preserves integer stratification, proves that it commutes with
the open comprehension body and repeated universal closure, and establishes
the exact set equality

```lean
TheoryBridgeProbe.quote_NF :
  quoteFormula '' NFChoice.Foundation.NF.fst = NFNotWPP.NF
```

`SolutionBridge.quote_NF` exposes the same equality through the proof
translator's quotation function. This is equality of the entire theories,
not merely inclusion of one finite basis in another.

The corresponding conclusion equation is

```lean
SolutionBridge.quote_accepted_not_sourceWPP :
  quoteFormula
      (Nominal.lowerWff id (Wff.neg syn_wwpp)) =
    Formula.neg SourceWPPFOL
```

Applying the structural proof translator to `nfPrfNotSourceWPP` and rewriting
by these two exact equations yields the public theorem.

## Exact shared-surface contract

The public contract is:

1. The challenge file is `Challenge.lean`.
2. The required declaration is exactly `NFNotWPP.NF_proves_not_WPP`.
3. Its required type is exactly the type printed in the first section.
4. Every supporting declaration through `def SourceWPPFOL` is defined once in
   the proof-free `NFNotWPP.Surface` module. Challenge and Solution import the
   same compiled declarations.
5. A submission may replace only the final proof hole. It may not alter the
   frozen syntax, calculus, stratification predicate, comprehension schema,
   standard `NF`, exact source WPP, or lowering definitions.
6. A submitted solution must contain no `sorry`, `admit`, new `axiom`, opaque
   assumption, unsafe proof escape, or altered theorem type.

The shared module imports only Mathlib and contains no proof of the headline
theorem. Using one compiled surface prevents import-sensitive typeclass
elaboration from changing a definition between Challenge and Solution, while
still preventing a submission from shadowing the theorem name or proving a
similar statement over a weakened theory.

## Exact WPP and presentation fidelity

The target remains

```lean
def SourceWPPFOL : Formula := Nominal.lowerWff id Source.syn_wwpp
```

The copied `syn_wwpp` is the exact compact source expansion. Its ordered pair
is the NF source pair `syn_cop`, built through `syn_cphi`; it is not silently
replaced by the ordinary Kuratowski pair `syn_copk`. The source term is closed,
with a reduction-checkable certificate `SourceWPP_closed : syn_wwpp.fv = ∅`,
so the initial environment has no mathematical effect. `id` is used because
it makes the accepted nominal-proof instantiation literal.

Two lossless presentation changes remain:

1. Membership is a primitive `Formula.mem x y` node rather than Flypitch's two
   nested `apprel` nodes over its sole binary relation symbol.
2. Closed intrinsically scoped formulas are erased to the raw `Nat`-indexed
   syntax before entering the public proof calculus; their indices are
   exactly the `.fst` formulas used by `Fol.SentTheory.fst`.

These are handled by structural quotation. They do not change the theory,
target formula, or proof rules.

## Comparator and release status

The local Challenge and prior standalone Solution builds and the final
three-axiom audit pass. Public run #10 completed the exact cold Solution build
and reached Comparator without an OOM. Comparator correctly rejected the old
duplicated surface because `freshVar` had elaborated with two definitionally
equivalent but structurally different lattice instances. The shared Surface
eliminates that entire import-order failure mode without adding a definition
hole. A protected Comparator/export/NanoDa rerun remains pending; no passing
Comparator result is claimed in this document.

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
proof-free statement surface or Challenge.
