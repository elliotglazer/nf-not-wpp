# Accepted intermediate chain

This directory contains the complete successful Metamath/MM0 artifact chain.
It is archival evidence and is not imported by Lean.

`metamath/` contains every distinct material state described in
`../README.md`. The accepted final state is canonical in
`../../provenance/metamath/accepted-translator-input.mm` and is duplicated
only where the historical translator layout requires it.

`mm0/successful-run/` is the successful conversion run for source SHA-256
`868DF831E63E28AA924CC099510CD9E5D3BE18CD8416A20B335F5BBF3B42ED3F`:

| Artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| `normalized_for_mm0.mm` | 9,945,172 | `AB4B33F9E9873B45B4CE504A9A7FC94AFB9DFE9464467AD5643D362AF945C454` |
| `direct.mm0` | 125,710 | `503D35EA113DFA50324F98709239ADC1F59F49F7C1C740DDCC2F3A902437E461` |
| `verified_text.mm0` | 125,710 | `503D35EA113DFA50324F98709239ADC1F59F49F7C1C740DDCC2F3A902437E461` |
| `verified_text.mmu` | 27,647,028 | `5EA04A13ECB096BC0B7765F899BFBFFE86B7C483AD17AB7C91434AE35B776AA7` |
| `proof.mmb` | 2,059,548 | `CD5AC6A064FB4D3E98A39392CB8FF2FEC89959890FF426E97B74D3CE53E04CFE` |
| `final_conversion_audit.json` | 37,782 | `338E391A2661BF70F34F136964ACF42A0531089B5E0CA2E5E0507E932F555D6B` |

The two `.mm0` names are byte-identical but both are kept: one is the direct
conversion output and the other is the result accepted by the textual
verification step. The `logs/` directory contains all 37 stdout, stderr,
verifier, and resource files from the successful run.

`receipts/` preserves the earlier flattening audit and the accepted MM0
translation manifest. They record the handoff into the material states and
the successful-run directory rather than another source state.

MM0 was an independent conversion/verification track. The Lean translator
consumes the accepted `.mm` directly; it does not silently trust or import the
`.mm0`, `.mmu`, or `.mmb` files.
