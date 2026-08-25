# Verification record

This is the retained pre-publication verification record for the local Palomar
candidate. It does not replace Palomar's protected Linux verifier.

## Statement boundary

- `Challenge.lean`: 827 physical lines, 34,394 bytes, SHA-256
  `719D3F180A22AFF950A3839145846FDDB4D1D7AC2E50385DCA90AD426F65FC5D`.
- `Solution.lean`: 1,862 physical lines, 76,085 bytes, SHA-256
  `427F4FACD2E7D722501736BD9E9BF322E105CDAFA5B143AC67B9BEC9554CC214`.
- The 793-line declaration region from `namespace NFNotWPP` through
  `SourceWPPFOL` is text-identical in the two files.
- The compared declaration is
  `NFNotWPP.NF_proves_not_WPP` at the exact type
  `NF ⊢ₛ' Formula.neg SourceWPPFOL`.
- Here public `NF` is extensionality plus every instance of the full
  stratified-comprehension schema. The eleven literal Hailperin sentences are
  retained only as the translated proof's internal finite-basis bridge.
- Solution does not import Challenge. Challenge imports only Mathlib.

## Source build

The candidate uses Lean `v4.30.0-rc2`, Mathlib
`83a5988a25fdd78621774a57af7e1f5c55f24289`, and Flypitch
`503dd00ba677b42628a878ad263cc116abb0a8f7`.

The historical translated-replay-closure build originated from an empty
`.lake` directory on a Windows x86-64 workstation. Lake scheduling was bounded
first at two and then, after measuring memory headroom, three jobs; every Lean
child used `--threads=1`. Two generated modules exhausted only Lean's
`constructorNameAsVariable` style-linter heartbeat budget after elaboration.
They were isolated in `NFNotWPPLinterHeavy` with the single override
`-Dlinter.constructorNameAsVariable=false`.

The first final-configuration Linux CI run then exposed one additional
non-semantic output issue: `WPPCompactSyntaxFVExplicit` emitted over fifteen
thousand lines of unused-simp-argument and generated-tactic diagnostics before
the standard runner sent `SIGTERM`. It is now isolated in the same target with
the five linter settings already embedded throughout the generated replay
modules,
and both large Linux jobs serialize Lake at `LEAN_NUM_THREADS=1`. None of these
settings changes declarations, generated source bytes, proof terms, or kernel
checking.

The resumed build compiled all 1,527 source modules in the translated C18
replay closure successfully. It predates the added `NFStandard` layer and the
migration of the public Challenge/Solution statement, so it is historical
closure evidence rather than a cold build of the current whole configuration.

This is not evidence of one uninterrupted cold build of the final staged Lake
configuration. That clean Linux run remains a release gate alongside
Comparator/export/NanoDa verification.

Observed timing results on 2026-08-24:

- artifact timestamps for the broader empty-origin effort span 4 h 02 min and
  include an unlogged 49 min 42 s pause after the first 82 modules;
- contemporaneous working notes record a 3 h 10 min diagnosis/resume window
  ending in final success; no raw timing log was retained, so neither figure
  should be treated as a clean benchmark;
- migrated final `Challenge.lean` warm compilation: 14.52 s wall time, with
  Lake reporting 11 s;
- migrated final `Solution.lean` warm compilation: 23.30 s wall time, with
  Lake reporting 18 s;
- warm `lake build NFStandard`: 10.814 s wall time; and
- warm default `lake build`: 3.918 s wall time.

Both final Lake target checks passed. No uninterrupted cold-build timing is
claimed for the migrated whole configuration.

The final axiom query reported exactly:

```text
'NFNotWPP.NF_proves_not_WPP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

Lexical and declaration audits found no Solution/proof `sorry`, `admit`,
`sorryAx`, custom `axiom`, `opaque`, `unsafe`, `partial`, `native_decide`, or
`Lean.ofReduceBool`. Challenge contains exactly its deliberate theorem whose
declaration starts at line 823 and whose `sorry` body is at line 825.

## Translator reproduction

The Palomar-compliant portable translator was tested in a relocated fixture
containing 174 files (12.57 MB) and exactly zero `.olean` files. With CPython
3.12, this command completed in approximately 111 seconds:

```text
python -B translation/reproduce_c18.py out/c18
```

The result regenerated all five C18 `.lean` files byte-for-byte against both
the historical outputs and `Proof/`. The portable v2 wrapper SHA-256 is
`D481332291549E844ACA557158DDBB6A55EBBB5F7250EA1E87E5D7C1E47EA2F5`;
the relocated run's output `resource.json` SHA-256 was
`561790BB3826959FB817E1E21A45BE89A6BB4D4B7039FF9457BF5A4AE076E288`.
The same public command then passed from the final candidate's long Windows
checkout in 123.8 seconds; that path-specific `resource.json` SHA-256 was
`60E9B948D3ACE14C95A3F32210C43848C2A2FBBDAB99FA7358C8CA3649F726B3`.
After the first public Linux run exposed POSIX treatment of the manifest's
frozen Windows source labels, the wrapper gained a scoped basename adapter.
A complete post-fix replay again emitted all five files byte-identically; its
path-specific `resource.json` SHA-256 was
`089989E0F16840B41596CF54783ACDD2B456F0CA1199370B826DCD116FDB79FA`.

`translation/archive/compiled_lean_evidence.json` replaces no proof source. It
records the paths, sizes, SHA-256 values, and hash-pinned JSON authorities for
77 historical alpha certificates and two profile certificates (21,417,512
historical bytes). Its SHA-256 is
`17532DD6BEBD20E3C45F110EE7CACAA1A69CFCB9784DB6E40CF0C30C40D224BD`,
and its ordered contract-set SHA-256 is
`859A4B86E3FEA2FCA57AB4EFA09B74ED06C04CBFEBB0D6D8D5AB055F42972AE4`.
All 79 original payloads were rehashed before exclusion from Git. The wrapper
rejects attempted binary reads and the resulting Lean source remains subject
to the independent kernel/Comparator checks.

## Source and repository integrity

- All 1,527 translated-replay closure-manifest rows exist in `Proof/` and match
  their recorded SHA-256 values.
- That historical C18 proof payload is 97,305,006 bytes and 699,761 physical
  source lines. These figures do not include the later `NFStandard` layer.
- The exact 12-page manuscript is present in TeX and PDF; the PDF is 357,483
  bytes with SHA-256
  `9B3BD8EB7AE23AD9C55029C262DE3DADADF9DA329D55E42C597C0A95860571B3`.
- The accepted intermediate archive contains every material Metamath state,
  the complete 44-file successful MM0 run (including all 37 logs), and 63
  retained reconstruction payload files.
- `scripts/verify-archive.py` rehashed 306 retained files totalling
  265,762,469 bytes with zero missing, extra, or mismatched entries.
  `archive/MANIFEST.sha256` has 306 lines, 54,294 bytes, and SHA-256
  `0ACA7BBB08D4D5A62AC61DFAF03C1EDA84AD7463A89E3F968531E89B81FFE3A8`.
- The final intended source snapshot contains 1,884 files and 373,793,823
  bytes (356.48 MiB). Its largest file is the 27,647,028-byte MM0 `.mmu`, and
  the snapshot remains below Palomar's 500-MiB repository limit.
- All ten Git dependencies use credential-free public GitHub HTTPS URLs and
  full lowercase 40-character revisions.
- Final static scans found no LFS pointer, submodule, Git symlink, forbidden
  compiled Lean/native artifact, cache/build directory, credential, or
  operative machine-local dependency. Historical receipts deliberately
  retain their original workstation labels, including 122 inert comments in
  the byte-exact Metamath input; the portable translator rebases those labels
  and the Lean build does not consume them. This was a scan of the intended
  tracked-plus-untracked source snapshot before its final commit; the public
  immutable commit remains subject to the same protected CI checks.
- The three shell entry points are recorded as executable and their syntax and
  Landrun-wrapper regression pass under Git Bash.
- `formalization.yaml` contains no operative publication placeholder. Its
  author and responsible-maintainer lists both name Elliot Glazer and its
  repository SPDX identifier is `Apache-2.0`.
- Root `LICENSE` is byte-identical to the pinned Palomar starter text: 11,357
  bytes, SHA-256
  `C71D239DF91726FC519C6EB72D318EC65820627232B2F796219E87DCF35D0AB4`.
  This host has no Ruby runtime, so the exact Ruby metadata validator and
  Licensee detector remain part of the first public Linux CI run.

## Remaining protected and human gates

Comparator, `lean4export`, Lean-kernel replay, and NanoDa require Linux because
the pinned Landrun sandbox uses Landlock. This Windows host has neither a WSL
distribution nor Docker, Rust, Go, or a native linker, so the exact protected
pipeline is retained in `.github/workflows/ci.yml` and
`scripts/verify-comparator.sh` for the first public Linux run.

Elliot Glazer has confirmed the formalization author list,
responsible-maintainer list, Apache-2.0 repository licence, and public upload
to `https://github.com/elliotglazer/nf-not-wpp`. Before Palomar submission, he
must still approve the remaining metadata and explicitly authorize submission.
