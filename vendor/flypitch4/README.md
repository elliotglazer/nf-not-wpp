# Vendored Flypitch4 sources

This directory contains the exact Lean source files used from the public
Flypitch repository:

- repository: `https://github.com/ianklatzco/flypitch.git`
- commit: `503dd00ba677b42628a878ad263cc116abb0a8f7`
- upstream package path: `flypitch4/`
- upstream `Flypitch4/` Git tree: `75d83b51131e36c2580236b960efe8b3771e707a`
- upstream root-module Git blob: `4cef59928a657264d69ba128fbc7053edc7aa1ab`
- upstream licence Git blob: `261eeb9e9f8b2b4b0d119366dda99c6fd7d35c64`

The 25 `.lean` files are byte-for-byte copies. `LICENSE` is the upstream
Apache-2.0 licence. `SOURCES.sha256` independently fixes the bytes retained
here and is checked by CI.

Flypitch4 is compiled as a library of the repository's root Lake package. No
source declarations or proofs were modified. This layout avoids relying on a
Git-package `subDir` during sandboxed verification while preserving the same
module names and imports.
