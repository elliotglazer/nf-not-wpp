# Reusable nominal Metamath-to-Lean translator v1

`reusable_nominal_mm_translator_v1.py` turns a checked interval of the
canonical Metamath proof closure into append-only Lean source modules.  It
checks the Metamath proofs, replays their syntax trees, verifies every pinned
input, rejects unsupported leaves and generic DV fallbacks, and audits that the
split modules reconstruct the emitted theorem stream byte-for-byte.  It does
not start Lean; kernel checking is a separate step.

The reusable emitter composes the pinned, alpha-neutral
`CompactFVNormalizeMixin` ahead of the accepted structural-FV backend.  Every
setvar/nonset cache is therefore one deterministic `simp only` normalization
using audited FV equations and exact source/freshness facts; unsupported
support syntax or a missing atomic fact fails closed.  The resource records
the mixin hash and requires its normalization count to equal the nonmembership
cache census.  The mixin does not import or select an alpha frontier: the
frontier remains solely the runtime `--alpha-frontier-resource` input.

## Frozen profile selection

The CLI now defaults to `WPP_PROFILE_V2`.  V2 inherits all 92 V1 inputs
byte-for-byte and adds the verified global-alpha v3/a4972 source metadata for
B1..B71,W1 (global ordinal 72).  Existing command lines need no new required
argument.  Use `--wpp-profile WPP_PROFILE_V1` only when an exact legacy-profile
run is desired; `--wpp-profile WPP_PROFILE_V2` may be written explicitly in
archival scripts.

Profile V2 authorizes the translator's source backend.  It does not authorize
an alpha kernel frontier: `--alpha-frontier-resource` must still name a
separately accepted trust-zero, exact-three resource with recursively verified
oleans.  The selected profile identity and manifest hash are recorded in both
the source audit and output resource.

## Initial prefix

Supply both ordinal flags to select an interval.  Omitting both selects the
whole endpoint closure.  An interval starting at ordinal 1 is self-contained:

```powershell
python -B reusable_nominal_mm_translator_v1.py `
  --source path/to/source.mm `
  --source-sha256 SOURCE_SHA256 `
  --endpoint wppfiniteblocknotwppndv `
  --start-ordinal 1 --end-ordinal 250 `
  --alpha-frontier-resource path/to/accepted-alpha/resource.json `
  --alpha-frontier-sha256 ALPHA_RESOURCE_SHA256 `
  --output-dir path/to/fresh-output `
  --split-bytes 60000 `
  --module-prefix NominalWPPReplayPrefix001To250
```

The output directory must not already exist.  Each part imports the preceding
part, and the small umbrella module imports the last part.  A theorem larger
than the byte limit is preserved as one oversized singleton; theorem bodies
are never cut.

## Continuation interval

For an interval beginning after ordinal 1, also pin the immediately preceding
successful translator resource:

```powershell
python -B reusable_nominal_mm_translator_v1.py `
  --source path/to/source.mm --source-sha256 SOURCE_SHA256 `
  --endpoint wppfiniteblocknotwppndv `
  --start-ordinal 251 --end-ordinal 500 `
  --predecessor-resource path/to/prefix-250/resource.json `
  --predecessor-resource-sha256 PREDECESSOR_RESOURCE_SHA256 `
  --alpha-frontier-resource path/to/accepted-alpha/resource.json `
  --alpha-frontier-sha256 ALPHA_RESOURCE_SHA256 `
  --output-dir path/to/fresh-output --split-bytes 60000
```

The command fails unless the predecessor names the same source and endpoint,
ends exactly one ordinal before the new interval, and publishes a hash-matching
umbrella artifact.  A source-only predecessor is verified as a `.lean` source
boundary and is not represented as kernel-accepted.  A kernel predecessor must
additionally publish a successful exact-three trust-zero umbrella command, a
hash-matching `.olean`, and a pinned source-resource reference.

## Audit-only preflight

Add `--audit-only` to perform source checking and coverage analysis without
emitting Lean modules.  Audit-only still publishes `resource.json` in the
fresh, append-only `--output-dir`; it does not leave that directory reusable.
Use a different fresh output path for a later emission run.  `--split-bytes`
remains required so the audited emission boundary is explicit.

Version 1 accepts one flattened, hash-pinned Metamath source file.  It rejects
`$[ ... $]` includes rather than reading transitive files that are absent from
the source pin.

## Canonical three-theorem validation

The real-source validation in `rmmv1e2e1` selected closure ordinals 1 through
3 (`a1ii`, `mp2b`, `a1i`) at the accepted trust-zero alpha prefix 48.  With a
300-byte limit it produced three chained parts, including the expected
380-byte oversized singleton.  Its source-only resource is
`rmmv1e2e1/resource.json`, SHA-256
`A7E309822EC5455924D137472C2E7207D45413DB1B463E2452248D862984097E`;
the independent source audit is SHA-256
`BBFF923E098A2CF74D81852FD77A87C53D4FE5293F824F61CC7521F6999E2183`.

Version 1 deliberately supports the accepted NF/WPP syntax, FV,
primitive-leaf, and definition-alpha profile.  A different theory vocabulary
must add and audit a new target profile rather than silently falling back.
