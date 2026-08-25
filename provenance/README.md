# Provenance bundle

This directory keeps the content-addressed evidence needed to audit how the
packaged Lean proof relates to its Metamath source. None of these files is a
Lean build input.

The complete material research archive is indexed by
[`../archive/README.md`](../archive/README.md): it includes the informal paper,
all accepted Metamath/MM0 intermediates, and reconstruction tooling. The
portable and historical translator release is documented in
[`../translation/README.md`](../translation/README.md). This directory remains
the compact proof-closure and accepted-input boundary used by the Lean package.

- `METAMATH_PROVENANCE.md` is the human-readable source, repair, translation,
  and evidence-boundary account. SHA-256:
  `A38E44DA5451D2261D87643FF60F7624D9850CC5EDF8BCB94A8E802F93B1DED1`.
- `provenance.json` is the machine-readable 19-stage repair record and exact
  generated-output inventory. SHA-256:
  `DB2A59E6E75C1EDFCC52E3CADE69A704B7EB991C43604B7BFB6129389EA6EB2C`.
- `metamath/accepted-translator-input.mm` is the exact strict-scope-clean
  source consumed by the accepted translator. It is 9,945,323 bytes; SHA-256:
  `868DF831E63E28AA924CC099510CD9E5D3BE18CD8416A20B335F5BBF3B42ED3F`.
- `c18-source-closure.tsv` is a sanitized, repository-relative inventory of
  every packaged translated-replay module, its selected source hash, selection
  method, and direct-import count. It has 1,537 data rows; SHA-256:
  `483D3E1E12DD2AFECC1878559ECFE7EE298254B7936025C005D9F8ABFC3D1B21`.

The historical extraction selected 1,527 modules. Of those, 1,526 remain at
their original packaged paths and hashes. The remaining generated module is
preserved byte-for-byte under `translation/reference/` and deterministically
packaged as ten chained shards plus its original import name, producing the
current 1,537-row inventory. `scripts/verify-source-closure.py` rehashes every
row against `Proof/`; `translation/reproduce_wpp_fv_split.py` independently
checks the frozen monolith, the 143-name manifest, dependency order, shard
hashes, and packaged bytes.

The exact translator input intentionally preserves 122 inert `Linear replay
source:` comments containing historical `C:/Users/glaze/...` workstation
labels (lines 86,934 through 96,829). They are comments, not active Metamath
includes or Lean/runtime dependencies. Silently rewriting them would destroy
the accepted-input hash, so the publication bundle retains and explicitly
whitelists them; the derived closure TSV above is the sanitized inventory for
portable source selection.

The upstream `nf.mm` content is pinned to the last set.mm commit that changed
that file, `c1814c4fbaf88d329d7d73ec1c7358647570e435`, and SHA-256
`727A3707545E13EC53F03502EB07DC4635A8C176F275D4014A17FBD823E66083`.
The historical whole-repository checkout of the uploaded copy is not known;
the exact uploaded bytes are known and match that immutable upstream blob.
