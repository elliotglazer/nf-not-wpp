# Verification record

This is the retained pre-publication verification record for the local Palomar
candidate. It does not replace Palomar's protected Linux verifier.

## Statement boundary

- `Challenge.lean`: 777 physical lines, 32,621 bytes, SHA-256
  `C11A4D460ECA22BE99ACF19557BD63D15B43A17EF3596982E096B3680C303CA1`.
- `Solution.lean`: 1,640 physical lines, 67,390 bytes, SHA-256
  `85E6A14A23AE79FC997E4F42FC9BACCAAE831DF659D45A2F4E03CAC9A3BACE85`.
- The 745-line declaration region from `namespace NFNotWPP` through
  `SourceWPPFOL` is text-identical in the two files.
- The compared declaration is
  `NFNotWPP.hailperinNF_proves_not_WPP` at the exact type
  `LiteralHailperinNF ⊢ₛ' Formula.neg SourceWPPFOL`.
- Solution does not import Challenge. Challenge imports only Mathlib.

## Source build

The candidate uses Lean `v4.30.0-rc2`, Mathlib
`83a5988a25fdd78621774a57af7e1f5c55f24289`, and Flypitch
`503dd00ba677b42628a878ad263cc116abb0a8f7`.

The local source-only build originated from an empty `.lake` directory on a
Windows x86-64 workstation. Lake scheduling was bounded first at two and then,
after measuring memory headroom, three jobs; every Lean child used
`--threads=1`. Two generated modules exhausted only Lean's
`constructorNameAsVariable` style-linter heartbeat budget after elaboration.
They were isolated in `NFNotWPPLinterHeavy`. That Lake target adds exactly one
override, `-Dlinter.constructorNameAsVariable=false`; pre-existing
generated-source linter settings and all proof-checking options are unchanged.
The final build resumed the same source-created cache and compiled all 1,527
packaged proof modules successfully.

This is not evidence of one uninterrupted cold build of the final staged Lake
configuration. That clean Linux run remains a release gate alongside
Comparator/export/NanoDa verification.

Observed timing results on 2026-08-24:

- artifact timestamps for the broader empty-origin effort span 4 h 02 min and
  include an unlogged 49 min 42 s pause after the first 82 modules;
- contemporaneous working notes record a 3 h 10 min diagnosis/resume window
  ending in final success; no raw timing log was retained, so neither figure
  should be treated as a clean benchmark;
- `lake build Challenge Solution` from the completed proof tree: 24.5 s;
- final post-metadata warm `lake build Challenge Solution`: 6.8 s;
- post-archive packaging `lake build Challenge Solution`: 91.2 s, successfully
  replaying all 2,585 reported jobs after the local cache state had changed;
- warm default `lake build`: 3.9 s;
- direct `--trust=0 --threads=1` Challenge recompilation: 15.3 s;
- direct `--trust=0 --threads=1` Solution recompilation: 35.6 s.

The final axiom query reported exactly:

```text
'NFNotWPP.hailperinNF_proves_not_WPP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

Lexical and declaration audits found no Solution/proof `sorry`, `admit`,
`sorryAx`, custom `axiom`, `opaque`, `unsafe`, `partial`, `native_decide`, or
`Lean.ofReduceBool`. Challenge contains exactly its deliberate theorem hole.

## Translator reproduction

The Palomar-compliant portable translator was tested in a relocated fixture
containing 174 files (12.57 MB) and exactly zero `.olean` files. With CPython
3.12, this command completed in approximately 111 seconds:

```text
python -B translation/reproduce_c18.py out/c18
```

The result regenerated all five C18 `.lean` files byte-for-byte against both
the historical outputs and `Proof/`. The portable v2 wrapper SHA-256 is
`100FB1C07DB0450FDE10194B826609A711D8CC144159F6943C72580E9FEB4B9B`;
the relocated run's output `resource.json` SHA-256 was
`561790BB3826959FB817E1E21A45BE89A6BB4D4B7039FF9457BF5A4AE076E288`.
The same public command then passed from the final candidate's long Windows
checkout in 123.8 seconds; that path-specific `resource.json` SHA-256 was
`60E9B948D3ACE14C95A3F32210C43848C2A2FBBDAB99FA7358C8CA3649F726B3`.

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

- All 1,527 closure-manifest rows exist in `Proof/` and match their recorded
  SHA-256 values.
- The proof payload is 97,305,006 bytes and 699,761 physical source lines.
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
- The intended Git snapshot contains 1,868 files and 373,627,855 bytes
  (356.319 MiB); the largest is the 27,647,028-byte MM0 `.mmu`. Its forbidden
  compiled-suffix scan found zero files. Seventy-nine local `.olean` recovery
  copies remain ignored and are not part of the submitted snapshot.
- All ten Git dependencies use credential-free public GitHub HTTPS URLs and
  full lowercase 40-character revisions.
- Static scans found no LFS pointer, submodule, symlink/reparse point,
  forbidden compiled Lean/native artifact outside `.lake`, credential, or
  operative machine-local dependency. Historical receipts deliberately retain
  their original workstation labels, including 122 inert comments in the
  byte-exact Metamath input; the portable translator rebases those labels and
  the Lean build does not consume them.
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
responsible-maintainer list, and Apache-2.0 repository licence. Before
publication, he must still approve the remaining metadata, provide the public
repository destination, and authorize upload and submission.
