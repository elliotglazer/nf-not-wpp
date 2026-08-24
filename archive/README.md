# Research archive

This directory preserves the non-Lean side of the NF refutation of WPP. It is
not imported by the proof. Its purpose is to make the paper-to-Metamath-to-MM0
history independently inspectable and to keep every distinct file on the
accepted conversion path.

The phrase **all intermediate files** means all material states and receipts
on the successful, accepted path. Failed exploratory branches are not bundled.
Byte-identical aliases are normally represented once, except where two names
in the successful MM0 run record distinct verification steps. A redundant RAR
copy of that run is omitted because it contains no additional artifact.

## Contents

- `paper/` contains the exact TeX and rendered PDF of Elliot Glazer's
  manuscript, plus the ledger connecting its mathematical blocks to the final
  Metamath theorem.
- `upstream/nf.mm` is the exact CC0 upstream NF database used as the basis.
- `intermediates/metamath/` contains the standalone project extension, the
  comment-bearing and comment-free standalone databases, every distinct
  accepted repair state, the proof-only donor branch, and the physical-helper
  state used immediately before the final scope repair.
- `intermediates/mm0/successful-run/` contains the complete successful MM0
  conversion: normalized source, both named `.mm0` results, `.mmu`, `.mmb`,
  the final audit, and all 37 log/receipt files.
- `intermediates/receipts/` contains the accepted flattening audit and MM0
  translation-acceptance manifest at the boundary between those two tracks.
- `reconstruction/` preserves the stage receipts, builders, auditors, proof
  fragments, and MM0 runners under their original project-relative paths.
- `third_party/mm0/` records the pinned MM0 source revision and its CC0 notice.
- `../translation/archive/` preserves the exact historical translator layout,
  profiles, receipts, C17/C18 boundaries, and the 79-entry textual compiled-
  evidence ledger used by the portable launcher.
- `MANIFEST.sha256` content-addresses this archive and the frozen translator
  archive. Run `python scripts/verify-archive.py` from the repository root.

The exact final Metamath input is already canonical at
`provenance/metamath/accepted-translator-input.mm`; the portable translator
also retains a byte-identical copy at its historical path. Git deduplicates
identical payloads internally.

## Material Metamath states

The repair account and hashes for states 00–18 are recorded in
`provenance/provenance.json`; state 17a is the additional retained physical-
helper checkpoint whose full hash is recorded by this archive manifest and its
reconstruction audit. The filenames here impose a readable order:

| State | File | SHA-256 prefix | Meaning |
| --- | --- | --- | --- |
| 00 | `00-flattened-commented.mm` | `DD1E4E77` | verified flattened source |
| 01 | `01-private-dv-scoped.mm` | `E39E2B6B` | private DV scoping |
| 02 | `02-proofs-compressed.mm` | `751DC9B8` | all proofs compressed |
| 03 | `03-binding-metadata-overlay.mm` | `F7A8B4B3` | MM0 binding metadata |
| 04 | `04-active-hypotheses-relabeled.mm` | `DFFA1C07` | 22 formula-identical relabels |
| 05 | `05-endpoint-slice.mm` | `CE980762` | endpoint/parser closure |
| 06 | `06-fdminvalp-scope-repair.mm` | `B0018F20` | `fdminvalp` repair |
| 07 | `07-pointcover-scope-repair.mm` | `B52CC759` | point-cover proof repair |
| 08 | `08-pwpull-scope-repair.mm` | `D4161B3B` | pullback proof repair |
| 09 | `09-hnqinc-scope-repair.mm` | `BD113CBB` | quotient-inclusion repair |
| 10 | `10-cfb-codecover-scope-repair.mm` | `DE0C790F` | code-cover repair |
| 11 | `11-df-lnwmap-syntax-repair.mm` | `EE2E4C26` | one syntax correction |
| 12 | `12-wppstop-scope-repair-donor.mm` | `F9AC32DF` | proof-only donor branch |
| 13 | `13-df-lnwmap-wppstop-merge.mm` | `60271E6C` | base/donor merge |
| 14 | `14-hnwcut-quotient-proxy-stage1.mm` | `6969776C` | first quotient helper |
| 15 | `15-hnwcut-quotient-proxy-stage2.mm` | `24A5D458` | second quotient helper |
| 16 | `16-hnwcut-strict-quotient-stage3.mm` | `BE2D112F` | strict quotient helper |
| 17 | `17-hnwcut-factor-value-stage5.mm` | `2BBB76DD` | factor/value helper group |
| 17a | `17a-hnwcut-physical-helpers-before-final.mm` | `E88B80A2` | final physical helpers |
| 18 | `18-hnwcut-final-physical-scope-repair.mm` | `3A05D138` | final proof/scope repair |
| 19 | `provenance/metamath/accepted-translator-input.mm` | `868DF831` | importer cleanup; accepted input |

The historical name “stage5” at state 17 does not indicate a missing accepted
state; it was the experiment's local label. State 12 is deliberately retained
because state 13 is a two-parent merge.

## Exclusion rule

The archive omits failed MM0 importer trials, transient caches, package
checkouts, compiled Lean/native build products, compiled tool executables, and
duplicate manuscript aliases. These are not inputs to the accepted proof. In
particular, the omitted successful-run RAR file is only a compressed container
for files preserved individually. Historical `.olean` identities survive as
path/size/SHA-256 contracts in textual translator receipts; the portable
translator does not need their binary payloads. No omitted file is needed by
`translation/reproduce_c18.py`, the Lean build, or the archive verifier.

## Licence boundary

Project-authored paper, proof extensions, scripts, receipts, and documentation
are covered by the repository's Apache-2.0 grant from Elliot Glazer. Upstream
`nf.mm` and MM0 are CC0; their notices are preserved. The historical journal
articles cited by the paper are linked but not redistributed. See
[`../translation/THIRD_PARTY.md`](../translation/THIRD_PARTY.md) for the
complete boundary.
