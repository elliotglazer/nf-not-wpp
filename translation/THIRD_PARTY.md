# Third-party and licence notices

The root Apache-2.0 licence covers project-authored code, generated proof
sources, the project manuscript, repair scripts, receipts, and
documentation. The following boundaries are retained explicitly.

## Metamath NF database

The upstream portion of the accepted Metamath source is `nf.mm` from
`metamath/set.mm`, pinned to commit
`c1814c4fbaf88d329d7d73ec1c7358647570e435`. Its own header dedicates the work
to the public domain under CC0 1.0. The exact bytes and notice are preserved at
`archive/upstream/nf.mm`.

## MM0

MM0 is pinned to `digama0/mm0` commit
`697060e119ab3f4f1a8dae4451f5cbacd9803626`, under CC0. Its exact notice is at
`archive/third_party/mm0/LICENSE.txt`. No MM0, Stack, GHC, or platform
executable is redistributed.

## Lean, Mathlib, and Flypitch

The Lean source proof derives from the repository's pinned Lean 4, Mathlib,
and Flypitch inputs. Lean 4, Mathlib, and the pinned Flypitch checkout carry
Apache-2.0 licences. Exact revisions are in `lean-toolchain` and
`lake-manifest.json`.

Historical translator receipts name 79 `.olean` certificates and retain each
certificate's path, byte count, and SHA-256. Their binary payloads are not
redistributed: Palomar forbids committed Lean build products, and the
translator never deserialized them. The portable launcher verifies the
textual contract instead, while the emitted Lean source is independently
checked by the current source build in `Proof/`.

## CPython

CPython is not bundled. The portable launcher requires a separately installed
CPython 3.12.x and uses only its standard library. The Python installation is
subject to the Python Software Foundation licence supplied by its distributor.

## Historical literature

Hailperin (1944), Specker (1953), and da Silva (2021) are cited and linked in
the paper documentation. Their articles are not copied into this repository.
