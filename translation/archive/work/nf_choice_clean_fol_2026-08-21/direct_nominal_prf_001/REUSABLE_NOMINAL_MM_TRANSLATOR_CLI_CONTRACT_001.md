# Reusable nominal Metamath-to-Lean translator: CLI contract v1

Status: source-only design. This document does not authorize or perform a Lean
run, and it does not modify any accepted producer.

## Scope

The first reusable CLI should target the already supported NF/WPP language and
proof algebra. It is not yet a universal compiler for an arbitrary Metamath
database: the target Lean syntax constructors, FV equations, nominal logical
axiom wrappers, and definition-leaf wrappers must already have accepted
manifests/modules.

Within that boundary, source parsing, compressed-proof checking, closure
selection, proof-DAG replay, substitution, structural DV certificate emission,
alpha-frontier dispatch, theorem-boundary splitting, and manifest generation
are already implemented. The new work is primarily configuration and
orchestration.

## Existing stack to reuse

1. `compiler/mm_parser.py`
   - `Database.parse(path)` parses includes and checks every `$p` proof.
   - `Database.dependency_closure(endpoint)` returns the exact assertion closure
     in source order.
2. `compiler/ast_replay.py`
   - `ASTReplayer.replay_closure(endpoint)` reconstructs schemas and audits the
     endpoint DAG.
3. `direct_nominal_prf_001/emit_nominal_replay.py`
   - `NominalEmitter` supplies the `Nominal.NPrf` theorem interface, logical/NF
     leaves, recanonicalization, and exact theorem-call lowering.
4. `nf_wpp_clean_fol_2026-08-21/compiler/
   emit_wpp_compact_replay_fv_dispatch_v5.py`
   - `WPPCompactEmitterExactRepeatedRootFV` is the complete search-free
     structural FV/Disjoint certificate compiler used by the cached chunk-9
     witness.
5. `direct_nominal_prf_001/compact_fv_normalize_mixin_v1.py`
   - alpha-neutral, fail-closed normalization for every setvar/nonset cache;
     it uses audited FV equations and exact atomic facts in one deterministic
     `simp only` and delegates the other DV sort cases to v5.
6. `direct_nominal_prf_001/nominal_alpha_dispatch_core_v2.py`
   - `AlphaFrontier.load(resource, sha256, end_ordinal)` already follows the
     accepted-resource parent chain, honors reflected module overrides, checks
     olean hashes, and derives imports/olean roots.
7. `direct_nominal_prf_001/direct_nominal_structural_fv_v1.py`
   - proves that the nominal proof algebra and v5 structural-DV emitter compose;
     its `emit_theorem` cache policy should be retained.
8. `direct_nominal_prf_001/
   split_nominal_wpp_prefix37_cached_structural_fv_chunk009_60k_v1.py`
   and `split_nominal_wpp_chunk010_v1.py`
   - contain the byte-exact theorem parser, greedy theorem-boundary grouping,
     oversized-singleton rule, chained imports, umbrella module, and reversible
     hash census.

The current prefix-37 and chunk-9 wrappers are provenance successors, not the
right public API. In particular, they mutate imported module globals and then
delegate to a producer whose source, endpoint, chunk plan, frontier, and output
layout are fixed.

## Public CLI

Proposed entry point:

```text
python emit_nominal_mm_replay_v1.py
  --source PATH
  --source-sha256 HEX64
  --endpoint LABEL
  [--start-ordinal N --end-ordinal M]
  --alpha-frontier-resource PATH
  --alpha-frontier-sha256 HEX64
  --output-dir PATH
  --split-bytes N
  [--predecessor-resource PATH --predecessor-resource-sha256 HEX64]
  [--module-prefix NAME]
  [--namespace NAME]
```

`--start-ordinal` and `--end-ordinal` are one-based ordinals within the `$p`
theorem subsequence of the selected endpoint closure, not raw database
statement ordinals. Omitting both selects the full closure. Supplying only one
is an error.

An endpoint is still required when an ordinal interval is selected: without an
endpoint there is no canonical dependency-closure order. If `start-ordinal` is
greater than one, the predecessor resource is mandatory and must certify the
same source hash and endpoint, end exactly at `start-ordinal - 1`, and publish
the umbrella module imported by the first new part. This is the one additional
input needed to make a partial interval fail closed.

`module-prefix` and `namespace` may default to the current WPP values only when
the supplied source/surface profile is the pinned WPP profile. They must be
explicit for any other accepted profile.

## Fail-closed contract

Before creating the output directory, the CLI must:

1. Validate every supplied SHA-256 and refuse an existing output or staging
   directory.
2. Parse and kernel-independently verify the complete Metamath database.
3. Require `endpoint` to be a proved `|-` statement and replay its exact AST.
   Record the AST rather than hardcoding `(wn wwpp)`.
4. Derive the closure theorem list and validate the selected ordinal interval.
5. Load the accepted alpha frontier from its supplied path/hash. Derive its end
   ordinal from `firstUsePrefix.endOrdinal`; require an accepted exact-three
   kernel status and a consistent parent chain.
6. Validate the accepted target-surface/FV profile. For v1 this is the pinned
   WPP compact syntax and 143-head FV manifest.
7. If selection starts after ordinal one, validate the predecessor resource as
   described above and reject any source/endpoint/ordinal mismatch.
8. Pre-scan every selected proof application. Report the first unsupported
   logical axiom, NF literal axiom, definition leaf, alpha ordinal, syntax head,
   or FV head before writing output.
9. Emit every theorem in source order with every emitted label inserted into
   `cache_dv_labels`. Compose the pinned alpha-neutral compact-FV mixin first
   in the emitter MRO; require its certificate count to equal the complete
   setvar/nonset cache census. Reject any missing atomic fact or invocation of
   the generic DV fallback.
10. Reject `axiom`, `opaque`, `sorry`, `admit`, `native_decide`, or `unsafe` in
    generated text.

After emission, the CLI must:

1. Greedily group whole theorem declarations under `split-bytes`. A declaration
   larger than the limit is allowed only as an intact singleton.
2. Chain each part to the accepted predecessor or immediately previous part.
3. Add exactly one `#print axioms` for the final theorem of every part and an
   umbrella importing the final part.
4. Reconstruct the aggregate theorem region byte-for-byte from the parts.
5. Record source/resource/profile hashes, exact labels, proof-op hashes,
   application/substitution/dependency traces, alpha imports/olean roots,
   per-part hashes, aggregate theorem-body hash, structural certificate census,
   fallback count, and forbidden-token census in `resource.json`.
6. Write into a staging directory first and atomically rename it to the requested
   append-only output only after all static checks pass.

No Lean process belongs in this CLI. Kernel compilation remains a separate
consumer of the generated resource.

## Internal design

Add one public CLI and two small, importable helpers; do not patch accepted
producers in place.

### `parameterized_nominal_structural_emitter_v1.py`

Create a class factory taking an `AlphaFrontier` and endpoint/profile object.
The resulting class should inherit the alpha-neutral compact-FV mixin first,
then the nominal emitter and v5 structural-FV emitter, store the frontier on
`self`, dispatch accepted definitions through
`self.alpha_frontier.definition_leaf_call`, and cache every theorem's DV
targets. The mixin itself imports no frontier or endpoint. This removes the
import-time dependency on
`nominal_alpha_dispatch_prefix37_v2.py`.

The profile object owns support imports, target syntax/FV manifests, literal
leaf modules, namespace, and optional predecessor conventions. The initial
profile is a hash-pinned `WPP_PROFILE_V1`; profiles are data, not a chain of
Python successor wrappers.

### `nominal_replay_partition_v1.py`

Factor the byte-oriented `split_blocks`, `group_blocks`, header/footer builder,
and reconstruction audit out of the chunk-9/chunk-10 splitters. It accepts
theorem `(label, ordinal, bytes)` records and never knows a chunk number.

### `emit_nominal_mm_replay_v1.py`

Own argument validation and the transaction:

```text
pin inputs -> parse/check MM -> replay endpoint -> select closure interval
-> load frontier/profile -> pre-scan coverage -> emit theorem blocks
-> partition -> static audit -> publish resource/output
```

It should instantiate classes directly. It must not replace `TARGET` globals,
temporarily monkeypatch a module class, or infer inputs by globbing.

## Minimal hardcoded seams still blocking broader reuse

Only four mathematical interfaces remain hardcoded after the orchestration is
factored:

1. **Target surface/FV registry.** The v5 chain imports `wpp_config` and requires
   the exact 143-entry WPP FV manifest. A new source vocabulary needs accepted
   Lean syntax constructors and FV equations plus a manifest mapping each
   definition head to its fully qualified FV lemma.
2. **Nominal leaf registry.** `NominalEmitter.logical_leaf` explicitly handles
   the FOL rules and eleven NF literal axioms, while `definition_leaf` explicitly
   handles the non-alpha exceptional definitions (`df-clab`, `df-cleq`,
   `df-clel`, `df-tru`). This is sufficient for the current NF/WPP family, but a
   genuinely different theory needs a manifest/plugin for its primitive leaves.
3. **Alpha call-map universe.** `nominal_alpha_dispatch_core_v1.py` pins the
   current 71-base-definition call-map manifest. The frontier resource is
   already dynamic inside that universe; a different definition universe needs
   a different accepted call-map profile.
4. **Endpoint-dependent rule extraction in the WPP base constructor.** The base
   WPP emitter reads the global `ENDPOINT`. The successor should initialize the
   same fields from the CLI endpoint/profile rather than mutating that global.

The exact WPP endpoint string, `(wn wwpp)` AST assertion, 4,321 theorem count,
254/250 theorem chunk schedule, chunk-9 restriction, prefix-37 module, chunk-9
module names, and 60,000-byte constant are orchestration hardcodes, not
mathematical blockers. The proposed CLI deletes all of them.

## Implementation and effort

For the current NF/WPP profile:

1. Parameterized frontier/emitter adapter and coverage pre-scan: 2-3 focused
   hours.
2. Generic theorem-boundary partition helper and resource schema: 1-2 hours.
3. CLI transaction, append-only tests, and exact chunk-9 equivalence audit:
   2-3 hours.

Estimated source implementation: **5-8 focused engineering hours**. Once an
accepted alpha resource covers a requested range, generating it should take
roughly the existing emitter's runtime (minutes, not days); Lean kernel checks
remain separate machine time.

Generalizing beyond the accepted NF/WPP vocabulary is a different task because
it must construct and kernel-accept new Lean syntax/FV and primitive-leaf
profiles. That is not solved merely by changing CLI arguments.
