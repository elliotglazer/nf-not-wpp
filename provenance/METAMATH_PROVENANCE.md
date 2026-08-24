# Metamath provenance for the accepted C18 endpoint

Audit date: 2026-08-24. All SHA-256 values below were rechecked against the
artifacts still present in the project workspace. “Receipt” means a checked-in
JSON audit produced during the conversion; it is evidence, not a substitute
for the artifact hash.

## Upstream `nf.mm`

The project began from an uploaded copy of the New Foundations Explorer
database:

- archive path: `work/NF_WPP_complete_project_archive_2026-08-16/uploads_normalized/nf.mm`
- size: 2,985,424 bytes
- SHA-256: `727A3707545E13EC53F03502EB07DC4635A8C176F275D4014A17FBD823E66083`
- original upload name recorded by the archive:
  `52d068cf-64af-4c1e-b9d4-3c54ebc0df12.mm`

That file is byte-for-byte identical to upstream `nf.mm` at commit
[`c1814c4fbaf88d329d7d73ec1c7358647570e435`](https://github.com/metamath/set.mm/commit/c1814c4fbaf88d329d7d73ec1c7358647570e435),
the last commit touching `nf.mm` before this project and still the latest such
commit when audited. Immutable file links:

- [GitHub blob](https://github.com/metamath/set.mm/blob/c1814c4fbaf88d329d7d73ec1c7358647570e435/nf.mm)
- [raw bytes](https://raw.githubusercontent.com/metamath/set.mm/c1814c4fbaf88d329d7d73ec1c7358647570e435/nf.mm)

The raw upstream bytes at that URL were independently downloaded and hashed:
2,985,424 bytes and the same SHA-256 above. A later clean official checkout at
`b263d6e45b460ace961dea8839c953be7034adb4` also contains the same Git blob and
same bytes.

This proves the upstream **file-content revision**. It does not recover the
historical whole-repository checkout commit used when the user uploaded the
file: the upload/archive retained no `.git` metadata. Any claim that the upload
itself was checked out exactly at `c1814c4…` would therefore be stronger than
the evidence.

## WPP source and token identity

The upstream `nf.mm` does not itself contain the project’s final WPP
refutation. The project added its own verified Metamath extension and flattened
the include tree.

- Include entry point: SHA-256
  `266B9DC2CBBA5ECCA2C0930BA4D12D026EF720E5947AD214153A6C40BF0B8F62`.
- Comment-bearing flattened database: 10,591,102 bytes, SHA-256
  `DD1E4E778EB2B023827AF2AFFB35E043482B538118CFFB1932BFA7642C00C751`.
  The flatten audit records 136 dependency files, no remaining includes, and
  two independent successful checks of 7,973 proofs / 16,074 statements.
- Published comment-free twin: 9,037,362 bytes, SHA-256
  `8BE8C92D49838B719BA65B226CCC923BD4511FB8CFE388684F6C062A964E56F0`.
- After deleting comments and normalizing whitespace, the two standalone
  databases have the same 838,534-token stream, SHA-256
  `FC39C23CB7154F754B6D65C427BB9BDDB35F2BFBC2FF7048967CB981E9777D93`.

The custom extension’s authoring history is preserved as workspace files and
audits, not as an immutable public Git commit. That is an unresolved
publication-level provenance item, even though the final flattened bytes and
their verification are pinned.

## Material normalization and repair chain

The accepted translator input was not the published standalone file. The
following is the complete material chain used to make an importer-clean,
strict-scope-clean endpoint source. All proof-only repairs below were checked
with 0 trusted proofs; unless explicitly noted, assertion formulas, essential
hypotheses, and distinct-variable conditions were unchanged.

1. **Private DV scoping.** `DD1E4E…` -> `E39E2B6…`. Two formerly global
   `$d` environments were scoped privately over the assertions that inherited
   them. No assertion or proof tokens were rewritten.
2. **Proof compression.** `E39E2B6…` -> `751DC9B…`. All 217 remaining normal
   proofs were converted to compressed form; all 7,973 proofs were then
   compressed and no assertion expression changed.
3. **MM0 binding metadata overlay.** `751DC9B…` -> `F7A8B4B…`. A 394-byte
   `$j` comment block was appended. It changed zero Metamath tokens.
4. **Formula-identical active-hypothesis relabeling.** `F7A8B4B…` ->
   `DFFA1C0…`. Twenty-two compressed-proof table entries were changed from
   inactive `$e` labels to unique active labels with byte-identical formulas.
   No assertion or compressed proof-code token changed. The exact 22 mappings
   are in `wppfiniteblocknotwpp_mm0_hyp_label_repaired22.manifest.json`
   (receipt SHA-256
   `AE1DB6A9F3247848ADA1D034F980BAD5DE64CBCE3B2B2C9AF5D1CC35485F31E7`).
5. **Endpoint slicing.** `DFFA1C0…` -> `CE98076…`. The slicer blanked 3,644
   unrelated `$p` statements in place and retained 4,329 parser-closure proofs.
   Every retained theorem statement and proof token stayed identical; no
   retained theorem was promoted to an axiom.
6. **`fdminvalp` scope repair.** `CE98076…` -> `B0018F2…`. It added the
   active essential `fdminvalpbr.1 : |- C e. _V` and regenerated the five
   endpoint-closure proofs `fdminvalpbr`, `fdpivmap2ex`, `fdpivrange2ex`,
   `fdminvalpss`, and `elfdminvalp`.
7. **Strict-scope proof rebuilding.** The following proofs alone were rebuilt,
   with assertion structure unchanged:
   `cfbhnpw13pointcoverndv` (`B0018F2…` -> `B52CC75…`),
   `pwpullwesetimpndv` (`B52CC75…` -> `D4161B3…`),
   `hnqinctrnvaldndv` (`D4161B3…` -> `BD113CB…`), and
   `cfbhnqinjcodecoverddndv` (`BD113CB…` -> `DE0C790…`).
8. **`df-lnwmap` syntax repair.** `DE0C790…` -> `EE2E4C2…`. This is the one
   recorded assertion-formula edit: corrected function-value
   parenthesization in `df-lnwmap`; no proof changed and no downstream proof
   regeneration was required.
9. **WPP-stop strict-scope proof.** A proof-only donor rebuild changed
   `wppstopfixedhitcontrgrowfixdndv` (`DE0C790…` -> `F9AC32D…`). Merging that
   proof into the `df-lnwmap`-repaired base produced `60271E6…`.
10. **HNWCut helper lemmas.** Starting from `60271E6…`, 23 complete proved
    `$p` helper theorems were inserted, not axioms: three quotient-proxy
    helpers (`6969776…`, `24A5D45…`, `BE2D112…`), ten factor-value/ambient
    helpers (`2BBB76D…`), and ten final factor/range helpers. The resulting
    source `3A05D13…` also replaces only the proof of
    `hnwcutambstrictsegresisomralias0ndv`; its assertion and mandatory DVs are
    unchanged. The receipt reports 4,352 verified proofs, 0 trusted, and zero
    strict-scope rejections.
11. **Importer cleanup.** `3A05D13…` -> `868DF831…`. Three proof-table lists
    were deduplicated by one token each; the closed-scope floating declaration
    `hnwcutcodeeq-vx $f setvar x $.` was deleted and its proof-table reference
    retargeted to the active `vx`. The audit records zero changes to assertion
    formulas, essential hypotheses, or DV conditions.

Full hashes, sizes, receipt hashes, exact repaired theorem names, and the 23
inserted helper labels are in `provenance.json` beside this file.

## Accepted translator input and endpoint

- Translator input: 9,945,323 bytes, SHA-256
  `868DF831E63E28AA924CC099510CD9E5D3BE18CD8416A20B335F5BBF3B42ED3F`.
- Strict source census: 12,486 statements; 4,352 replayed `$p` proofs;
  0 trusted; 0 inactive-scope references.
- Endpoint label: `wppfiniteblocknotwppndv`.
- Exact Metamath expression: `|- -. WPP`.
- Mandatory hypotheses: 0; mandatory DV pairs: 0.
- Nominal AST: `(wn wwpp)`; AST SHA-256
  `600DA6FBC50032822E82069EA55CF2CD389162CC050681A3BECF5412079F69D5`.
- Semantic `|-` theorem ordinal: 4,321. C18 spans ordinals 4,255–4,321
  (67 theorems), so its final theorem is the endpoint.

## Translator and C18 identity

The accepted final endpoint receipt pins the C18 resource at SHA-256
`44CCEF5B0AB6594EFDC867BF8E59A7B3A7EA37D5BD3235DECB3293AC52F80D75`.
Its producer stack is:

- `reusable_nominal_mm_translator_v3.py`:
  `DECC5089EAB55B95806EB74742FD47A1EB127502B243811DD882737FCB98475F`
- pinned v2 predecessor:
  `52ED85A33329D1D4CE0E9D05622F74917E1CD9662959AAD7D7B6175244F34615`
- pinned v1 core:
  `8ABE386FEC8BEE78499D25B3B488C4C81054019590789CC1AF71D4DC352F3A94`
- compact FV backend:
  `CA7493053B75FC9B2EDC0F6C16AE31DE07C5F1A52119F15314BD09D3A165BDA4`
- frozen `WPP_PROFILE_V2` manifest:
  `96B6A85D4B5B60023000C49BB40CF4F7DCD679AAF4DB6C796880A684DBF12949`
- profile input-set digest:
  `E2CEA5925FB6A69A00544A01138356AC66C15B0CF614CF824D954BDB26725FF5`

The C18 receipt records 1,227 theorem applications, application-trace SHA-256
`B3354FF6DCEEF17BAE2C4A31F4CECD87FF7B1C56382E19346DD04B0CDAB4760A`,
seven deterministic FV normalizations, and zero generic DV fallbacks. The four
generated part files and umbrella are individually hashed in
`provenance.json`. These emitter normalizations affect generated Lean proof
terms; they do not mutate the pinned Metamath input.

## Evidence boundary

Verified by receipts and rehashing: every local artifact/hash above, the
flatten/token-identity claims, the stated repair deltas, strict replay counts,
endpoint expression/AST/ordinal, translator/profile identities, and generated
C18 hashes.

Verified against upstream bytes: `nf.mm` at `c1814c4…` is exactly the uploaded
`727A370…` file.

Unresolved: (1) the exact whole-repository checkout commit used for the
original upload, and (2) an immutable public VCS commit for the project-authored
WPP extension and its repair scripts. These gaps do not make the accepted C18
source ambiguous—the exact input and every accepted output are content-hashed—
but they should be closed before claiming fully reproducible public-source
provenance.
