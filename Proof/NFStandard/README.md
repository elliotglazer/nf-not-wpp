# Standard NF, Hailperin NF, and `NF ⊢ ¬WPP`

This directory contains the presentation-equivalence layer connecting the
repository's accepted Metamath replay to a conventional first-order theory of
New Foundations.

## Public theories and result

All declarations below use the membership/equality language `LNF`.

- `NFChoice.Foundation.NF` is the conventional theory: extensionality plus
  every stratified-comprehension instance. It is defined in `Basic.lean`.
- `NFChoice.Foundation.HailperinNF` is the repository's original finite
  Hailperin presentation, defined in `NFChoiceFoundation/Basic.lean`.
- `NFChoice.Foundation.ExactLiteralTrial.LiteralHailperinNF` is the exact
  intrinsic lowering of the eleven finite axioms used by the generated
  replay. `HailperinPresentationBridge.lean` proves that it and
  `HailperinNF` have the same models and consequences.
- `NFChoice.Foundation.NFStandard.WPP` is the closed Flypitch sentence obtained
  by exactly lowering the accepted nominal WPP source.

The main theorem is:

```lean
NFChoice.Foundation.NFStandard.NF_proves_not_WPP :
  NFChoice.Foundation.NF ⊢ₛ' Fol.bd_not NFChoice.Foundation.NFStandard.WPP
```

Thus the final statement is a Flypitch derivation from conventional `NF`:
extensionality and the stratified-comprehension schema in the ordinary
first-order equality calculus. It does not retain the Hailperin axioms as
extra assumptions.

## Proof architecture

The proof has two model-theoretic directions.

1. **Standard NF to the finite basis.** `ToHailperin.lean` constructs each
   Hailperin operation by a certified stratified-comprehension instance and
   proves `nf_models_literalHailperin`. The presentation bridge then gives
   `nf_models_HailperinNF`.
2. **The finite basis to standard NF.** `HailperinModel.lean` extracts semantic
   Skolem operations from the literal axioms. `HailperinCylinder.lean`,
   `HailperinUnitUnion.lean`, and `HailperinAlgebra.lean` use those operations
   to construct `hailperinCylinderAlgebra`. `CylinderCompiler.lean` compiles
   every capped stratified formula to a set of encoded valuations, and
   `CylinderToNF.lean` turns that compiler into all comprehension instances.

`Equivalence.lean` combines the directions. Its main declarations are:

```lean
literalHailperin_models_NF
models_NF_iff_literalHailperinNF
nf_literalHailperin_deductivelyEquivalent
hailperin_models_NF
nf_models_HailperinNF
models_NF_iff_HailperinNF
nf_hailperin_deductivelyEquivalent
```

`TheoryEquivalence.lean` uses Flypitch completeness to turn equality of model
classes into equality of formal consequences. `NotWPP.lean` first packages the
accepted nominal replay as `literalHailperin_proves_not_WPP`, transports it to
the repository presentation as `hailperin_proves_not_WPP`, and finally applies
`nf_hailperin_deductivelyEquivalent` to obtain `NF_proves_not_WPP`.

## The cylinder compiler

For one stratified formula, `CylinderCompiler.lean` chooses a single integer
type ceiling. Coordinate `i` is normalized by
`Int.toNat (cap - ty i)` singleton applications. `HailperinCylinder.lean`
encodes the resulting homogeneous vector as a nested Kuratowski tuple and
proves injectivity and coordinate recovery.

The concrete algebra implements:

- empty set, complement, and intersection from Hailperin NAND;
- equality and membership atoms from the subset relation, singleton image,
  `Ins2`, `Ins3`, and coordinate-selector recursion;
- exact Kuratowski image via the semantic form of Metamath's `dfimak2`;
- existential projection by raised image;
- parameter specialization by image followed by iterated unit union.

The cap is unchanged below quantifiers. Consequently the compiled set has the
exact law `mem_compile`, and `CylinderAlgebra.mem_comprehensionSet` supplies the
required standard comprehension object.

## Module guide

| Module | Role |
| --- | --- |
| `Basic.lean` | Stratification, comprehension instances, `NF`, and semantic eliminators |
| `StratificationNormalize.lean` | Elementary finite type-ceiling lemmas |
| `ToHailperin.lean` | Standard NF implies the exact finite basis |
| `HailperinPresentationBridge.lean` | Equivalence of the original and exact-literal finite presentations |
| `HailperinModel.lean` | Semantic operations extracted from the eleven literal axioms |
| `HailperinCylinder.lean` | Singleton normalization, tuple codes, image, composition, and relation primitives |
| `HailperinUnitUnion.lean` | Exact inverse to singleton raising |
| `CylinderCompiler.lean` | Abstract cap-aware stratified-formula compiler |
| `HailperinAlgebra.lean` | Concrete `hailperinCylinderAlgebra` implementation |
| `CylinderToNF.lean` | Any extensional cylinder algebra models `NF` |
| `TheoryEquivalence.lean` | Model inclusion/equality to formal consequence transport |
| `Equivalence.lean` | Public NF–Hailperin equivalence theorems |
| `WPP.lean` | Exact closed lowering of WPP |
| `NotWPP.lean` | Replay soundness and `NF_proves_not_WPP` |

## Verification and trust audit

From the repository root, the principal standalone checks are:

```text
lake env lean Proof/NFStandard/HailperinAlgebra.lean
lake env lean Proof/NFStandard/Equivalence.lean
lake env lean -DmaxHeartbeats=5000000 -DmaxRecDepth=30000 Proof/NFStandard/NotWPP.lean
```

The larger recursion limit in the final command is needed only to elaborate
the large generated replay term. On a warm build, the algebra and equivalence
checks take seconds; the final wrapper is typically under a minute.

The key modules contain `#print axioms` audits. For
`hailperinCylinderAlgebra`, `nf_hailperin_deductivelyEquivalent`, and
`NF_proves_not_WPP`, Lean reports only:

```text
[propext, Classical.choice, Quot.sound]
```

There are no project-specific opaque axioms or `sorry` placeholders in this
layer.
