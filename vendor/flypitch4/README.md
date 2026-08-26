# Vendored Flypitch4 sources

This directory contains the Lean source files used from the public Flypitch
repository, plus the minimal compatibility edits required by stable Lean 4.30:

- repository: `https://github.com/ianklatzco/flypitch.git`
- commit: `503dd00ba677b42628a878ad263cc116abb0a8f7`
- upstream package path: `flypitch4/`
- upstream `Flypitch4/` Git tree: `75d83b51131e36c2580236b960efe8b3771e707a`
- upstream root-module Git blob: `4cef59928a657264d69ba128fbc7053edc7aa1ab`
- upstream licence Git blob: `261eeb9e9f8b2b4b0d119366dda99c6fd7d35c64`

Twenty-one of the 25 `.lean` files are byte-for-byte copies. Four files have
only the mechanical edits enumerated in [`COMPATIBILITY.md`](COMPATIBILITY.md).
`LICENSE` is the upstream Apache-2.0 licence. `SOURCES.sha256` independently
fixes the current bytes retained here and is checked by CI.

Flypitch4 is compiled as a library of the repository's root Lake package. No
theorem statement or proof term was modified. This layout avoids relying on a
Git-package `subDir` during sandboxed verification while preserving the same
module names and imports.
