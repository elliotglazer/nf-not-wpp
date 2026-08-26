# Stable Lean 4.30 compatibility edits

The vendored baseline is Flypitch commit
`503dd00ba677b42628a878ad263cc116abb0a8f7`. Stable Mathlib 4.30 made three
source-compatible API reorganizations after the release candidate used by
that snapshot. This repository applies only these four mechanical edits:

1. `Flypitch4/ToMathlib.lean` imports
   `Mathlib.SetTheory.Cardinal.Cofinality.Ordinal` after Mathlib split the old
   `Mathlib.SetTheory.Cardinal.Cofinality` aggregate module.
2. `Flypitch4/Collapse.lean` uses the same replacement import.
3. `Flypitch4/PSetOrdinal.lean` names the successor alternative of
   `Ordinal.limitRecOn` `add_one` instead of its former name `succ`.
4. `Flypitch4/Forcing.lean` supplies `Finset.toSet` as an abbreviation for the
   existing `Finset`-to-`Set` coercion after Mathlib removed that deprecated
   spelling.

No theorem statement, tactic proof, proof term, or logical assumption changes.
`lake build Flypitch4` checks the complete vendored library under the pinned
stable toolchain, and `SOURCES.sha256` fixes the post-compatibility bytes.
