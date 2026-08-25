# NF proves not-WPP

This is a source-complete Palomar packaging candidate for a Lean 4 proof of the
theorem

```text
NF ⊢ ¬WPP.
```

Here `NF` is the standard first-order theory of extensionality plus the full
stratified-comprehension schema, and WPP is a classical choice principle.  The
repository also proves that `NF` is fully deductively equivalent to
`HailperinNF`, the finite eleven-sentence presentation used by the translated
Metamath proof. The Lean build is source-only; a separate, non-imported
research archive preserves the informal paper and the successful Metamath/MM0
translation history.

Public repository: [`elliotglazer/nf-not-wpp`](https://github.com/elliotglazer/nf-not-wpp).

In the exact Metamath source spelling used here, WPP says that for all sets
`x` and `y`, if there is both a function from `y` onto `x` and a one-to-one
function from `y` to `x`, then there is a one-to-one function from `x` to `y`.
The compared Lean theorem constructs a formal derivation of the negation of
that sentence from standard NF. To the best of our knowledge, the headline
result `NF ⊢ ¬WPP` is novel. In 2023, Thomas Forster publicly described the
corresponding partition-principle question for NF as open
([MathOverflow](https://mathoverflow.net/a/449571/109573)). The formal theorem
therefore settles a specific question that was not resolved merely by the
classical fact that full choice fails in NF. Its natural audience includes
researchers in axiomatic set theory, New Foundations, formal logic, and proof
translation.
For context, Specker's 1953 paper established the classical failure-of-choice
phenomenon in NF ([doi:10.1073/pnas.39.9.972](https://doi.org/10.1073/pnas.39.9.972)),
while the standard “Weak Partition Principle” terminology and its
surjection/injection formulation are discussed by da Silva
([doi:10.1093/jigpal/jzaa023](https://doi.org/10.1093/jigpal/jzaa023)). The
repository's exact theorem source remains the content-addressed Metamath proof
identified below.

> **Status:** proof complete; final packaging checks are in progress. The
> standard-NF theorem, the full `NF`/`HailperinNF` equivalence, the exact
> Challenge/Solution proof, and the C18 source closure are present. The public
> theorem passes a trust-zero audit with exactly the three permitted axioms.
> Public CI run #10 completed the full cold build in about 2 h 42 min without
> an OOM and reached Comparator. Comparator then exposed an import-sensitive
> elaboration mismatch in the formerly duplicated statement surface. The
> Challenge remains self-contained with only Mathlib imports, as Palomar's
> dependency policy requires; Solution now imports a proof-free mirror compiled
> under that same clean import environment before loading the proof library.
> A protected Comparator/export/NanoDa rerun remains pending. Authorship, maintenance
> responsibility, Apache-2.0 licensing, and public upload are confirmed;
> Palomar submission remains under the responsible maintainer's control.

## Headline theorem and finite-basis equivalence

The standard-theory development under `Proof/NFStandard/` exports the two
principal results:

```lean
theorem NFChoice.Foundation.NFStandard.NF_proves_not_WPP :
    NF ⊢ₛ' Fol.bd_not WPP

theorem NFChoice.Foundation.NFStandard.nf_hailperin_deductivelyEquivalent :
    DeductivelyEquivalent NF HailperinNF
```

`HailperinNF` is the existing finite presentation in the repository.  The
translated proof uses an exact token-level expansion named
`LiteralHailperinNF`; the development proves that these two spellings have the
same models and the same formal consequences before connecting the finite
basis to standard NF. Both headline declarations audit to exactly `propext`,
`Classical.choice`, and `Quot.sound`.

## Palomar public statement

`Challenge.lean` directly defines a small membership-only first-order language,
the eight primitive Flypitch-style proof constructors, the ordinary integer
stratification relation, the full stratified-comprehension schema, standard
`NF`, and a transparent lowering of the exact source WPP formula. Its sole
deliberate proof hole is:

```lean
theorem NFNotWPP.NF_proves_not_WPP :
    NF ⊢ₛ' Formula.neg SourceWPPFOL
```

This is a claim of **syntactic derivability**, not a model construction or a
consistency claim. Here `NF` is visibly extensionality plus every certified
stratified-comprehension instance. The eleven Hailperin formulas remain in the
statement surface only as a transparent description of the translated finite
basis; they are neither assumptions of the headline theorem nor Lean axioms.

The Challenge compiles and is 827 lines / 34,394 bytes, below Palomar's hard
limits of 1,000 lines / 100 KiB. It imports only the three canonical Mathlib
modules at its head. Solution imports an 811-line proof-free mirror whose
declaration region is byte-identical to Challenge and is compiled under the
same three Mathlib imports before the proof dependency is loaded. Thus the
compared constructors elaborate to identical constant information without a
candidate-local import in Challenge's closure. On its proof side, Solution
derives every literal Hailperin axiom from standard NF
using the proved model inclusion and first-order completeness, substitutes
those derivations for the axiom leaves of the accepted C18 replay, and
structurally translates the resulting `Fol.prf` term into the Challenge
calculus.

The packaged Solution compiles at trust zero without global heartbeat or
recursion-depth overrides. `#print axioms` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorry`, `admit`, custom
`axiom`, or `opaque` declaration. `comparator.json` permits exactly those three
axioms and requires NanoDa replay.

## Translated replay closure

The proof root is `NominalWPPReplayChunk018Compact001`; its accepted endpoint is
`NFChoice.DirectNominalPrf.WPPReplay.g_wppfiniteblocknotwppndv`. The exact
dependency audit for the accepted translated replay found:

- 4,706 transitive modules in the complete search closure;
- 1,527 historical translated-replay source modules selected before the
  handwritten `NFStandard` equivalence layer was added;
- 97,305,006 historical source bytes and 699,761 physical source lines;
- no missing or ambiguous imports, no source-hash mismatch, and no mismatch
  against the accepted ordered source search; and
- eleven module-name collisions, all resolved by the accepted receipt's
  deterministic source precedence (four byte-identical, seven divergent).

An independent post-copy hash pass checked all 1,527 historical files with
zero mismatches. To bound one Lean process's peak memory, the exact generated
`WPPCompactSyntaxFVExplicit` monolith is now preserved under
`translation/reference/` and deterministically packaged as ten chained shards
plus its original import facade. All 143 theorem bodies, fully qualified names,
and dependency order are retained. The other 1,526 files remain byte-identical;
the current packaged closure therefore has 1,537 modules and 97,308,251 bytes.
`scripts/verify-source-closure.py` rehashes that full inventory, while the
splitter independently checks the frozen monolith and manifest. Generated Lean
artifacts and local caches are not part of the source payload.

## Immutable inputs

The Lake package currently pins:

| Input | Revision |
| --- | --- |
| Lean | `leanprover/lean4:v4.30.0-rc2` |
| Mathlib | `83a5988a25fdd78621774a57af7e1f5c55f24289` |
| Flypitch (`flypitch4`) | `503dd00ba677b42628a878ad263cc116abb0a8f7` |

`lake-manifest.json` was generated by Lake and resolves all ten Git packages to
full immutable SHAs. The public Flypitch pin and its `flypitch4` subdirectory
layout have been built independently. The selected Lean version is supported
by the matching pinned `lean4export` revision used by the verification script.

The immutable upstream Metamath basis is
[`nf.mm` at its last content-changing set.mm commit `c1814c4fbaf88d329d7d73ec1c7358647570e435`](https://github.com/metamath/set.mm/blob/c1814c4fbaf88d329d7d73ec1c7358647570e435/nf.mm),
whose SHA-256 is
`727A3707545E13EC53F03502EB07DC4635A8C176F275D4014A17FBD823E66083`.
That basis file is byte-identical to the later archived checkout used during
translation; the archive did not record its whole-repository commit. The
translated endpoint is not in upstream `nf.mm`: it is theorem
`wppfiniteblocknotwppndv`, ordinal 4321, in the packaged project extension
inside `provenance/metamath/accepted-translator-input.mm`. The complete repair
account, translator/profile hashes, exact accepted input, C18 receipts, and
evidence boundary are summarized in `provenance/METAMATH_PROVENANCE.md` and
`provenance/provenance.json`, with the material artifacts preserved under
`archive/` and `translation/archive/`. The exact
9,945,323-byte translator input intentionally retains 122 inert historical
workstation-path comments to preserve its accepted hash;
`provenance/README.md` documents that exception, and no build step consumes
those labels.

## Research archive and translator

The repository includes the complete successful-path material requested for
independent study:

- [`archive/paper/`](archive/paper/README.md) contains the exact authorless
  12-page informal manuscript in TeX and PDF, plus the contract ledger that
  maps its proof blocks to `wppfiniteblocknotwppndv`;
- [`archive/intermediates/`](archive/intermediates/README.md) contains every
  distinct accepted Metamath state, the successful MM0 conversion with its
  `.mm0`, `.mmu`, and `.mmb` outputs, and all 37 run receipts;
- [`archive/reconstruction/`](archive/reconstruction/README.md) contains the
  retained repair builders, auditors, proof fragments, and MM0 runners;
- [`translation/`](translation/README.md) contains the hash-pinned historical
  translator stack, its frozen profiles and textual evidence, the portable
  one-command C18 reproducer, and the deterministic WPP FV source packager;
  and
- [`archive/MANIFEST.sha256`](archive/MANIFEST.sha256) content-addresses the
  complete archive. `scripts/verify-archive.py` verifies every retained byte.

The archive intentionally includes all material states and receipts on the
accepted successful path, not failed exploratory branches or redundant
containers. Its exact inclusion rule and licensing boundary are documented in
[`archive/README.md`](archive/README.md).

With CPython 3.12, the final translator chunk can be regenerated without Lean:

```text
python translation/reproduce_c18.py build/c18-replay
python translation/reproduce_wpp_fv_split.py
```

The first command replays the 4,321-theorem Metamath closure, emits C18, and
checks all five generated Lean files byte-for-byte against both the historical
output and `Proof/`. The second byte-checks the memory-bounded packaging of the
generated FV support monolith. Both use source/textual inputs rather than
bundled Lean build products, so the submitted tree contains no `.olean` files.

## Reproduction and release gates

The intended clean Linux verification sequence is:

```bash
lake exe cache get
lake build Challenge
LEAN_NUM_THREADS=1 lake build NFNotWPPProof
LEAN_NUM_THREADS=1 lake build NFStandard
LEAN_NUM_THREADS=1 lake build Solution
LEAN_NUM_THREADS=1 bash scripts/verify-comparator.sh
```

The proof library contains many large independent modules. On a machine with
many logical cores relative to available RAM, use `LEAN_NUM_THREADS=1` to
bound Lake's worker scheduling; the proof target also passes `--threads=1` to
each Lean child. Lake can still overlap tasks when required by its scheduler,
so this setting is not a strict one-child serialization guarantee. It changes
scheduling only, not the proof or trust boundary.

Three generated module families are isolated in `NFNotWPPLinterHeavy`. After
successfully elaborating their declarations,
`NominalWPPReplayChunk009StructuralPart030` and
`NominalWPPReplayChunk009StructuralPart038` exhaust the constructor-name style
linter's private heartbeat budget. The original monolithic
`WPPCompactSyntaxFVExplicit` otherwise emits over fifteen thousand lines of
generated unused-tactic and simp-argument diagnostics and creates the largest
single-process elaboration peak. Its ten deterministic chained shards retain
the exact theorem bodies and public declaration names while bounding that
peak. The generated `CompactSyntaxFV` and `CompactSyntaxFVExplicit` support
roots are in the same isolated target so their non-semantic generated
diagnostics are suppressed too. The target changes no proof-checking option.

For Comparator's exact `lake build Solution` command, the Landrun wrapper first
builds, in order, `+WPPCompactSyntaxFVExplicitPart001`,
`+NFStandard.HailperinAlgebra`, `+NFStandard.Equivalence`,
`+NFStandard.NotWPPLiteralReplay`, `+NFStandard.NotWPP`, and
`+NFStandard.NotWPPPrfBridge`. Each isolated build uses the same Landrun
binary, restrictions, environment, and writable `.lake` directory as the full
build, and each must succeed before the wrapper executes Comparator's original
command unchanged. Other commands remain single-pass. The final result is now
split into a semantic replay/equivalence branch and the direct syntactic proof
bridge; `Solution` imports only the latter. This keeps every proof step inside
Comparator's sandbox and changes neither its command nor its trust checks.

CI runs #7 (`a2d512e`), #8 (`8543027`), and #9 (`23114e0`) left all five
non-Comparator jobs green. Run #9 completed all three then-configured
prebuilds. During the unchanged Solution build, `[1080/1085] Built
NFStandard.Consequences` was the final completed job; Lake's dependency graph
identifies `NFStandard.NotWPP` as its active successor. The final steady sample
recorded one Lean process at 15,171,700 KiB RSS with 231,548 KiB host memory
available, and the cgroup `oom_kill` counter then increased from zero to one.
This establishes a single-process out-of-memory kill rather than a Lean proof
or type error. The protected job now provisions a checked 12 GiB swap file and
records host and cgroup swap use alongside the existing telemetry.

The setup/Challenge stages, public Flypitch build, standalone Solution,
trust-zero proof check, final axiom audit, standard-NF target, and source-only
`NFNotWPPProof` rebuild all pass. Public run #10 also completed the exact cold
Solution build and export preparation without an OOM; its first Comparator
failure was the now-diagnosed `freshVar` elaboration mismatch in the old
duplicated surface. The earlier translated
replay-closure rebuild originated from an empty `.lake` state and ultimately
compiled every then-packaged module. Artifact timestamps span 4 h 02 min and
include an unlogged 49 min 42 s pause after the first 82 modules;
contemporaneous working notes record a 3 h 10 min diagnosis/resume window
ending in success. It predates the handwritten `NFStandard` layer, so an
uninterrupted cold build of the final configuration remains a release gate.

Before the clean-mirror refactor, separate warm checks took 14.52 s for
`Challenge`, 23.30 s for `Solution`, 10.814 s for `NFStandard`, and 3.918 s for
the default build. The proof-free mirror itself locally built in 15 s. These
are engineering observations, not cold benchmarks. The remaining
Comparator/kernel-export/NanoDa check requires a Linux Landlock environment
and is delegated to the pinned CI workflow.
Exact local timings, hashes, axiom output, and evidence boundaries are recorded
in [`VERIFICATION.md`](VERIFICATION.md).

The release repository does not depend on absolute local paths, local package
overrides, checked-in Lean/native build products, credentials, submodules, or
unresolved path-order selection. Historical receipts retain their original
workstation labels as evidence; the portable translator rebases those labels
and no Lean build input consumes them. See `PALOMAR_CHECKLIST.md` for the
remaining evidence gates.

## Remaining publication gates

Elliot Glazer is the confirmed formalization author and responsible
maintainer, and the repository is licensed under Apache-2.0. The remaining
human gates are final approval of the other metadata and authorization of the
Palomar submission. The remaining mechanical gates are the
uninterrupted Linux cold build and protected Comparator/export/NanoDa run.

After those gates pass on an immutable public commit, submission goes through the
[official Palomar form](https://submit.palomar-registry.org/).

## Authoritative packaging references

- [Palomar submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
- [Official Palomar starter template](https://github.com/PalomarRegistry/PalomarTemplate)
- [Palomar toolchain registry](https://github.com/PalomarRegistry/PalomarSubmission/blob/main/toolchains.json)
- [Lean Comparator](https://github.com/leanprover/comparator)
