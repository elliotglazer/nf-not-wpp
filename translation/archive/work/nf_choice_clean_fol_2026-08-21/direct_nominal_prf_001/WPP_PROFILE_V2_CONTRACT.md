# WPP_PROFILE_V2 portability contract

`WPP_PROFILE_V2.json` is the immutable source-only successor to the audited
`WPP_PROFILE_V1`.  Its first 92 input entries are byte-for-byte equal to V1's
complete static inventory.  V2 adds exactly five inputs:

- the V1 manifest itself, pinning the parent profile and its input-set digest;
- `nominal_alpha_dispatch_core_v3.py`;
- the a4972 B49..B71,W1 source manifest;
- the corresponding source-authorization audit; and
- the independent v3/a4972 source-join audit.

The resulting bounded inventory contains 97 unique workspace-relative files:
20 Python sources and 77 fixed data/evidence files.  The translator verifies
the V2 manifest hash before parsing it, verifies all 97 file hashes before any
backend import, checks that V1 is inherited byte-exactly, and only then imports
the v3 dispatcher from verified source with Python bytecode reads disabled.

## Global nominal-alpha contract

V2 binds global ordinals B1..B71,W1 through ordinal 72.  In particular:

- global ordinal 72 is WPP surface ordinal 1, label `df-iso`;
- the global record-order digest is
  `0E5231014445B25C31737A520C4F4516101E27E9BAAEF5543B264DC7388FD0D5`;
- the original source-hash-order digest is
  `FCDCD473111EAD48A6089E2049C0F273C106733CB90DBE87722C586F65726FFA`;
- the a4972 successor-source-hash-order digest is
  `F5A3BAD8C928365ACB77E6C442AD7063DE80DDBC0D95B47DC83FA9980302C854`;
- the 72-module import-chain digest is
  `157CF0DDB86EBDA8C4EE88973F45616639B890BFAC6C1E8D56521DD268CA192E`.

The a4972 metadata is source authorization, not kernel acceptance.  An alpha
frontier remains a runtime input and must independently satisfy the CLI's
trust-zero, exact-three, recursive resource/olean checks.  Thus selecting V2
does not turn a source-only alpha artifact into an accepted kernel frontier.

## CLI compatibility

No former option was removed or made newly required.  `--wpp-profile` is an
optional selector with `WPP_PROFILE_V2` as the CLI default.  Passing
`--wpp-profile WPP_PROFILE_V1` preserves the legacy backend explicitly.  V2's
v3 dispatcher delegates frontiers through B71 to the pinned v2 implementation,
so existing B1..B48 invocations retain the established alpha behavior while
recording the new profile identity.

Every source-audit and resource output records the selected profile ID,
version, manifest hash, input-set hash, and bounded census.  The translator
entrypoint remains outside the static profile to avoid a self-hash cycle and
is recorded separately as the producer of every output.

## Reproduction and updates

`build_wpp_profile_v2_manifest.py` reproduces V2 byte-for-byte and refuses to
overwrite a differing manifest.  V1 is never modified.  Any future extension
beyond global ordinal 72, or any change to the dispatcher/a4972 metadata,
requires a new profile version rather than refreshing V2 in place.
