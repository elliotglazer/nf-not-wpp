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
  every packaged project module, its selected source hash, selection method,
  and direct-import count. It has 1,527 data rows; SHA-256:
  `E9A6EE3268A914A4091A20EEFF4EAE3EB1D26D50F6D016B68CE612784A8A8838`.

The TSV is derived mechanically from the accepted closure audit after
removing workstation paths and compiled-artifact fields. A fresh verification
against `Proof/` rehashed all 1,527 rows with zero missing files or mismatches.

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
