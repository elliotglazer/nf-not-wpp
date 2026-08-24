# WPP_PROFILE_V1 portability contract

`WPP_PROFILE_V1.json` freezes the reusable translator's accepted NF/WPP
source-only backend.  The translator hashes the manifest before parsing it,
then verifies every listed file before importing any local backend module or
reading any fixed call-map/surface input.  A mismatch aborts before output.

The manifest contains 92 unique workspace-relative inputs:

- 19 Python sources in the complete local import graph, including the four
  transitive helpers omitted by the earlier `BACKEND_PINS` table;
- the definition-dispatch and exact-definition-call JSON files;
- all 64 alpha-call manifests in their exact update order;
- the global base-alpha call-map manifest;
- the WPP source-audit, syntax/FV manifests, accepted surface resource, and
  two accepted surface oleans that the existing preflight hashes.

The manifest also freezes the 12 emitted Lean support-import names, canonical
WPP source hash, 143-head FV contract, and base-alpha ordinal ceiling 71.
After import, the translator joins every loaded module and every backend data
constant back to the manifest paths, including the ordered 64-file alpha list.

## Bytecode policy

Python's `-B` option prevents `.pyc` writes but does not prevent `.pyc` reads.
Before importing the backend, the translator rejects preloaded local backend
modules and redirects bytecode lookup to a process-unique nonexistent path
while suppressing writes.  Thus the executed backend is compiled from the
source bytes that were just verified, rather than from an adjacent cache.

## Deliberately runtime-authorized inputs

These inputs cannot be frozen into one reusable static profile and retain
their existing independent authorization:

- `--source` is pinned by `--source-sha256`; Metamath includes are rejected;
- the alpha frontier is pinned by its CLI hash, exact-three trust-zero schema,
  recursively hashed parents, and referenced accepted oleans;
- an optional predecessor is pinned by its CLI hash and recursively verified
  source/kernel artifacts;
- the append-only output directory is not an input.

Lean support source files are outside this source-only closure because the
translator emits their module names but does not read them.  They remain the
kernel runner's responsibility.

The translator entrypoint cannot be listed inside a manifest whose hash it
itself pins without creating a hash cycle.  Every output already records the
entrypoint as `producer.path` and `producer.sha256`; the new `wppProfile` field
records the profile manifest hash and its full input-set digest.

## Compatibility and updating

No CLI arguments changed.  Existing invocations gain only fail-closed
preflight checks and additive `wppProfile` audit/resource fields.  The profile
resolves all paths relative to the translator's workspace, so the tree may be
moved as a unit without rewriting absolute paths.

`build_wpp_profile_v1_manifest.py` reproduces the inventory source-only and
refuses to overwrite a differing manifest.  Any intentional backend or data
change should create and review a new profile version rather than silently
refreshing `WPP_PROFILE_V1`.
