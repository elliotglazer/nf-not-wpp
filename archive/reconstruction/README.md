# Historical reconstruction support

The files below this README retain their original project-relative paths.
They comprise 22 stage receipts/verification records, 28 repair builders and
auditors, seven proof fragments, five Metamath/MM0 runners or verifiers, and
the upstream MM0 licence notice.

They are historical, hash-addressed tooling—not a polished public build
system. Several scripts encode the old workspace layout in receipts. The
portable Lean translator has a reviewed relocation layer; these earlier
repair scripts intentionally remain untouched so their original hashes and
evidentiary value are not lost.

Two reconstruction details deserve explicit mention:

1. State 13 was made with the generic
   `work/mm0_conversion_2026-08-20/source_repair/merge_scope_repair_proofs.py`.
   Its arguments were the state-11 base, a fresh output path, and
   `wppstopfixedhitcontrgrowfixdndv=<state-12 donor>`. The generated output is
   state 13, SHA-256 `60271E6C951F21307987923A565B6448927FF97C1EF3F10E189585B5B3E62168`.
2. Exact state 18 reconstruction requires
   `recover_frozen_3a05_and_save_ac63.py`,
   `hnwcut_final_physical_helper_suffix.mmfrag`, and
   `hnwcutambstrictsegresisomralias0ndv.proof_only.mmfrag`, together with the
   state-17 parent. The ordinary builder alone does not reconstruct the exact
   frozen `3A05D138…` bytes.

The successful MM0 orchestration script is
`work/mm0_conversion_2026-08-20/generated/run_final_conversion.ps1`. It records
the historical Windows tool locations and should be read as a receipt. For a
new run, obtain MM0 from the pinned CC0 source revision documented in
`../third_party/mm0/README.md`; platform executables are deliberately not
vendored.
