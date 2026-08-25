# Palomar packaging and verification checklist

Legend: `[x]` has retained, definitive evidence; `[~]` is partial or actively
in progress and does **not** count as passed; `[ ]` is unresolved, not run, or
requires a human decision.

## 1. Human-owned decisions

- [x] Confirm the formalization author: Elliot Glazer.
- [x] Confirm the responsible maintainer: Elliot Glazer.
- [x] Choose Apache-2.0 and make its SPDX identity agree with metadata.
- [x] Add exactly one conventional root `LICENSE` from the pinned Palomar
      starter revision.
- [ ] Approve the abstract, classifications, scope, acknowledgements,
      automation disclosure, source relationships, and review status.
- [x] Explicitly approve publication at `elliotglazer/nf-not-wpp`.
- [ ] Explicitly approve Palomar submission.

## 2. Exact source extraction

- [x] Compute the accepted C18 endpoint's exact dependency closure: 4,706 total
      modules, of which 1,527 are project sources.
- [x] Copy all 1,527 selected `.lean` sources into `Proof/`; independent
      post-copy SHA-256 validation found zero mismatches.
- [x] Resolve all eleven module-name collisions by the accepted receipt's
      deterministic source precedence; the ordered-search audit found zero
      mismatches.
- [x] Retain the exact source endpoint
      `NFChoice.DirectNominalPrf.WPPReplay.g_wppfiniteblocknotwppndv` and the
      Challenge representation of its eleven literal theory axioms as the
      internal finite-basis bridge to the public standard-NF theorem.
- [x] Pin upstream `nf.mm` to its last content-changing set.mm commit
      `c1814c4fbaf88d329d7d73ec1c7358647570e435`, file SHA-256
      `727A3707545E13EC53F03502EB07DC4635A8C176F275D4014A17FBD823E66083`.
- [x] Add the publication provenance bundle with the full 19-stage
      repair/normalization chain, translator/profile revisions, exact accepted
      Metamath input, sanitized closure manifest, and retained audit hashes.
- [x] Include the exact informal manuscript in TeX and PDF, its contract
      ledger, every material successful-path Metamath state, the complete MM0
      successful run, and the retained reconstruction builders and receipts.
- [x] Include and document the historical translator stack, frozen profile,
      textual compiled-evidence contract, and portable CPython 3.12 launcher;
      an exact C18 replay emits all five packaged Lean files byte-for-byte.
- [x] The final intended source-snapshot scan found no forbidden absolute
      dependency, local executable or package override, compiled artifact,
      cache, or experiment output. Historical archive receipts retain
      documented workstation labels, including 122 inert comments in the
      accepted Metamath input; the portable translator rebases its receipt
      paths, and no Lean build input consumes those labels.

## 3. Lake package

- [x] Pin and independently build public Flypitch commit
      `503dd00ba677b42628a878ad263cc116abb0a8f7` from subdirectory `flypitch4`.
- [x] Pin Mathlib commit `83a5988a25fdd78621774a57af7e1f5c55f24289`.
- [x] Generate `lake-manifest.json` with Lake; every effective Git `rev` is a
      full immutable SHA and every URL is public, credential-free HTTPS.
- [x] Pin Lean `v4.30.0-rc2` and verify that the matching `lean4export` revision
      is available in Palomar's supported toolchain path.
- [x] Finish an empty-origin, diagnosed/resumed source-only build of the
      historical translated-replay closure. It completed all 1,527 C18 closure
      modules, including two narrowly fixed style-linter diagnoses and
      scheduler restarts; every Lean child used `--threads=1`. Artifact
      timestamps span 4 h 02 min with a 49 min 42 s unlogged pause; working
      notes record a 3 h 10 min diagnosis/resume window. This predates
      `NFStandard` and is not final-configuration cold-build evidence.
- [ ] Run an uninterrupted final-configuration cold source-only build on Linux
      comparable to a Palomar worker.
- [ ] Optionally test a stable-toolchain upgrade; it is not required for the
      currently supported pinned toolchain.

## 4. Challenge/Solution boundary

- [x] Add a self-contained `Challenge.lean` whose transitive project-facing
      imports are Mathlib only.
- [x] Compile the Challenge with exactly one deliberate final-theorem hole. The
      theorem begins at line 823, and its `sorry` proof body is at line 825.
- [x] Keep the Challenge below Palomar's hard limits: 827 lines and 34,394
      bytes versus 1,000 lines and 100 KiB.
- [x] Define the membership-only syntax, eight primitive proof constructors,
      ordinary integer stratification, the full stratified-comprehension
      schema, standard `NF` as that schema plus extensionality, and the exact
      lowered source WPP. The eleven literal Hailperin formulas remain only as
      the internal translated finite-basis bridge.
- [x] State syntactic derivability of `Formula.neg SourceWPPFOL` under the public
      name `NFNotWPP.NF_proves_not_WPP`, at the exact type
      `NF ⊢ₛ' Formula.neg SourceWPPFOL`.
- [x] Configure distinct `Challenge` and `Solution` module names in Lake and
      `comparator.json`.
- [x] Prove the direct structural bridge from the accepted C18 nominal/Flypitch
      proof into the internal literal basis, then replace every finite-basis
      axiom leaf by its derivation from standard NF. The public endpoint
      compiles at the exact Challenge type and its axiom audit reports precisely
      the three permitted axioms.
- [x] Add standalone `Solution.lean` with the same public declaration name and
      exact type, no Challenge import, and a 793-line declaration prefix that
      is text-identical to the Challenge through `SourceWPPFOL`.

## 5. Trust and proof checks

- [x] Compile the packaged public Solution theorem and audit its dependencies;
      it reports only `propext`, `Classical.choice`, and `Quot.sound`.
- [x] Confirm the production Solution and selected dependency closure contain
      no `sorry`, `sorryAx`, custom `axiom`, or opaque proof assumption.
- [x] Confirm `#print axioms NFNotWPP.NF_proves_not_WPP` reports exactly
      `propext`, `Classical.choice`, and `Quot.sound`.
- [ ] Run Comparator and confirm exact Challenge/Solution statement identity.
- [ ] Export the public proof and have Lean's kernel accept it at trust zero.
- [ ] Replay the exported proof independently with NanoDa.
- [~] Retain tool revisions, commands, logs, elapsed time, and artifact hashes;
      exact migrated Challenge/Solution metrics, hashes, local compilation, and
      axiom evidence are recorded, as is the historical empty-origin replay
      closure build. The uninterrupted final-configuration Linux cold build and
      Comparator/export/NanoDa records remain outstanding.

## 6. Runtime and repository limits

- [~] Measure and stabilize the source build with bounded Lake scheduling. The
      historical empty-origin translated-replay closure completed. For the
      migrated final files, warm Challenge compilation took 14.52 s wall time
      (Lake reported 11 s), and warm Solution compilation took 23.30 s wall
      time (Lake reported 18 s). Warm `NFStandard` took 10.814 s and the warm
      default build took 3.918 s. No uninterrupted final cold-build timing is
      claimed.
- [x] Reproduce C18 with the portable source-only translator and confirm that
      all five emitted `.lean` files are byte-identical to the historical and
      packaged copies. The translator itself does not invoke Lean.
- [ ] Measure the full Comparator/export/NanoDa path on representative hardware
      and fit the ordinary Palomar allowance or arrange a larger worker.
- [ ] If measurements require it, coalesce generated modules without changing
      declarations or proof terms, then repeat every trust check.
- [x] The copied historical C18 proof payload is 97,305,006 bytes. The final
      intended source snapshot contains 1,884 files and 373,793,823 bytes
      (356.48 MiB), below the 500-MiB repository cap; its largest file is the
      27,647,028-byte retained MM0 `.mmu`.
- [x] The final intended source-snapshot scan found no Git LFS pointer,
      submodule, Git symlink, forbidden compiled Lean/native artifact,
      cache/build directory, secret, credential, or operative machine-local
      path. Protected CI must repeat release checks on the immutable commit.

## 7. Metadata and editorial review

- [x] Replace every operative `TODO(...)` in `formalization.yaml`; field-shape
      and schema validation remain covered by the validation item below.
- [x] Replace the moving Metamath metadata URL with the immutable
      `c1814c4fbaf88d329d7d73ec1c7358647570e435` content-changing commit.
- [x] Retain a content-addressed provenance account for every source repair,
      translator/profile revision, proof-only rebuild, and translation
      divergence; final human review remains part of the publication gate.
- [x] Content-address the paper, all retained intermediates, reconstruction
      materials, and frozen translator archive in `archive/MANIFEST.sha256`.
- [x] Report zero Solution/proof sorries, excluding only the one deliberate
      Challenge statement hole as Palomar directs.
- [x] Supply an accurate, non-promotional human/agent automation and cost
      disclosure, explicitly claiming no independent human peer review.
- [ ] Have a human audit the public standard-NF definition (extensionality,
      stratification, and the full comprehension schema), the internal eleven
      Hailperin bridge formulas, and the WPP target against the intended
      NF/Hailperin/Metamath syntax.
- [ ] Run the current Palomar metadata validator with no warnings or sentinels.

## 8. Publication and submission (never implicit)

- [x] Obtain explicit user approval to publish the repository.
- [x] Publish `https://github.com/elliotglazer/nf-not-wpp` without submodules.
- [ ] Run all checks against the exact public snapshot.
- [ ] Submit the public repository, immutable 40-character commit SHA, and
      root-relative `comparator.json` path through Palomar's official form.
- [ ] Review the generated public record and editorial report before permanent
      registration.
