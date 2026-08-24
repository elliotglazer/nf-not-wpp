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
- [ ] Explicitly approve publication and Palomar submission.

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
      Challenge representation of the eleven literal theory axioms.
- [x] Pin upstream `nf.mm` to its last content-changing set.mm commit
      `c1814c4fbaf88d329d7d73ec1c7358647570e435`, file SHA-256
      `727A3707545E13EC53F03502EB07DC4635A8C176F275D4014A17FBD823E66083`.
- [x] Add the publication provenance bundle with the full 19-stage
      repair/normalization chain, translator/profile revisions, exact accepted
      Metamath input, sanitized closure manifest, and retained audit hashes.
- [x] Complete the final whole-tree scan for absolute paths, local executable
      or package overrides, compiled artifacts, caches, and experiment output.
      The sole expected path exception is 122 documented, inert comments in
      the byte-exact accepted Metamath input; the portable closure inventory is
      sanitized and no build input consumes those labels.

## 3. Lake package

- [x] Pin and independently build public Flypitch commit
      `503dd00ba677b42628a878ad263cc116abb0a8f7` from subdirectory `flypitch4`.
- [x] Pin Mathlib commit `83a5988a25fdd78621774a57af7e1f5c55f24289`.
- [x] Generate `lake-manifest.json` with Lake; every effective Git `rev` is a
      full immutable SHA and every URL is public, credential-free HTTPS.
- [x] Pin Lean `v4.30.0-rc2` and verify that the matching `lean4export` revision
      is available in Palomar's supported toolchain path.
- [x] Finish an empty-origin, diagnosed/resumed source-only candidate build. It
      completed all 1,527 packaged modules, including two narrowly fixed
      style-linter diagnoses and scheduler restarts; every Lean child used
      `--threads=1`. Artifact timestamps span 4 h 02 min with a 49 min 42 s
      unlogged pause; working notes record a 3 h 10 min diagnosis/resume window.
- [ ] Run an uninterrupted final-configuration cold source-only build on Linux
      comparable to a Palomar worker.
- [ ] Optionally test a stable-toolchain upgrade; it is not required for the
      currently supported pinned toolchain.

## 4. Challenge/Solution boundary

- [x] Add a self-contained `Challenge.lean` whose transitive project-facing
      imports are Mathlib only.
- [x] Compile the Challenge with exactly one deliberate final-theorem `sorry`.
- [x] Keep the Challenge below Palomar's hard limits: 777 lines and 32,621
      bytes versus 1,000 lines and 100 KiB.
- [x] Define the membership-only syntax, eight primitive proof constructors,
      exactly eleven literal Hailperin formulas, and exact lowered source WPP.
- [x] State syntactic derivability of `Formula.neg SourceWPPFOL` under the public
      name `NFNotWPP.hailperinNF_proves_not_WPP`.
- [x] Configure distinct `Challenge` and `Solution` module names in Lake and
      `comparator.json`.
- [x] Prove the direct structural bridge from the accepted C18 nominal/Flypitch
      proof into the independent Challenge calculus; the isolated trust-zero
      endpoint compiles at the exact Challenge type with precisely the three
      permitted axioms.
- [x] Add standalone `Solution.lean` with the same public declaration name and
      exact type, no Challenge import, and a 745-line declaration prefix that
      is text-identical to the Challenge through `SourceWPPFOL`.

## 5. Trust and proof checks

- [x] Compile the packaged public Solution theorem at trust zero; it reports
      only `propext`, `Classical.choice`, and `Quot.sound`.
- [x] Confirm the production Solution and selected dependency closure contain
      no `sorry`, `sorryAx`, custom `axiom`, or opaque proof assumption.
- [x] Confirm `#print axioms NFNotWPP.hailperinNF_proves_not_WPP` reports exactly
      `propext`, `Classical.choice`, and `Quot.sound`.
- [ ] Run Comparator and confirm exact Challenge/Solution statement identity.
- [ ] Export the public proof and have Lean's kernel accept it at trust zero.
- [ ] Replay the exported proof independently with NanoDa.
- [~] Retain tool revisions, commands, logs, elapsed time, and artifact hashes;
      empty-origin diagnosed/resumed build evidence and local
      Challenge/Solution trust evidence are complete, while the uninterrupted
      final-configuration Linux cold build and Comparator/export/NanoDa records
      remain outstanding.

## 6. Runtime and repository limits

- [x] Measure and stabilize the source build with bounded Lake scheduling: the
      empty-origin diagnosed/resumed effort ultimately completed, warm
      Challenge+Solution took 24.5 s, and a warm default build took 3.9 s. The
      source-build observations above are not a clean benchmark because no raw
      timing log was retained.
- [ ] Measure the full Comparator/export/NanoDa path on representative hardware
      and fit the ordinary Palomar allowance or arrange a larger worker.
- [ ] If measurements require it, coalesce generated modules without changing
      declarations or proof terms, then repeat every trust check.
- [x] The copied proof payload is 97,305,006 bytes and the staged candidate is
      about 102.75 MiB, comfortably below the 500 MiB repository cap.
- [x] Scan the staged tree for Git LFS pointers, submodules, forbidden compiled
      artifacts, secrets, credentials, and machine-local paths; no unexpected
      findings remain.

## 7. Metadata and editorial review

- [x] Replace every operative `TODO(...)` in `formalization.yaml`; field-shape
      and schema validation remain covered by the validation item below.
- [x] Replace the moving Metamath metadata URL with the immutable
      `c1814c4fbaf88d329d7d73ec1c7358647570e435` content-changing commit.
- [x] Retain a content-addressed provenance account for every source repair,
      translator/profile revision, proof-only rebuild, and translation
      divergence; final human review remains part of the publication gate.
- [x] Report zero Solution/proof sorries, excluding only the one deliberate
      Challenge statement hole as Palomar directs.
- [x] Supply an accurate, non-promotional human/agent automation and cost
      disclosure, explicitly claiming no independent human peer review.
- [ ] Have a human audit the eleven Challenge formulas and WPP target against
      Hailperin/Metamath source syntax.
- [ ] Run the current Palomar metadata validator with no warnings or sentinels.

## 8. Publication and submission (never implicit)

- [ ] Obtain explicit user approval to publish the repository.
- [ ] Publish a public GitHub repository without submodules.
- [ ] Run all checks against the exact public snapshot.
- [ ] Submit the public repository, immutable 40-character commit SHA, and
      root-relative `comparator.json` path through Palomar's official form.
- [ ] Review the generated public record and editorial report before permanent
      registration.
