# Metamath-to-Lean translator

This directory contains both the exact historical translator and a portable
launcher for reproducing the final C18 Lean source.

From the repository root, with CPython 3.12:

```text
python translation/reproduce_c18.py build/c18-replay
```

On Windows, `py -3.12` may be used instead of `python`. The command is
source-only: it parses and replays Metamath and writes Lean source, but never
starts Lean. It then checks that all five generated C18 `.lean` files are
byte-identical to both the historical outputs and their packaged `Proof/`
copies. A successful run prints `PASS`.

The final zero-`.olean`, relocated replay took about 111 seconds on the
development machine. Startup and static profile validation are fast, but the
translator still replays the 4,321-theorem closure; this is not yet a
sub-second cached converter.

## What the translator does

The historical implementation is a deterministic, fail-closed pipeline:

1. Parse the accepted Metamath database and replay its proof stack.
2. Convert each supported Metamath syntax tree to the nominal/Flypitch Lean
   syntax constructors selected by the frozen WPP profile.
3. Translate proof applications to primitive `Fol.prf` constructors.
4. Discharge the profile's structural free-variable and distinct-variable
   obligations with explicit generated certificates.
5. Use the accepted alpha/frontier modules for the definition leaves already
   proved in Lean.
6. Emit source modules in a deterministic byte partition and write a detailed
   `resource.json`/`source_audit.json` receipt.

This is the operational form of the “syntax constructors” shortcut: there is
no semantic model or soundness/completeness detour. The generated proof is a
syntactic replay, and the final `Solution.lean` bridge instantiates its formula
constructors directly in the Challenge calculus.

## Historical stack

The untouched historical files live under `archive/work/...` so their own
relative path calculations still resolve:

| Component | SHA-256 |
| --- | --- |
| `reusable_nominal_mm_translator_v1.py` | `8ABE386FEC8BEE78499D25B3B488C4C81054019590789CC1AF71D4DC352F3A94` |
| `reusable_nominal_mm_translator_v2.py` | `52ED85A33329D1D4CE0E9D05622F74917E1CD9662959AAD7D7B6175244F34615` |
| `reusable_nominal_mm_translator_v3.py` | `DECC5089EAB55B95806EB74742FD47A1EB127502B243811DD882737FCB98475F` |
| `WPP_PROFILE_V2.json` | `96B6A85D4B5B60023000C49BB40CF4F7DCD679AAF4DB6C796880A684DBF12949` |

V1 is the reusable parser/replayer/emitter. V2 replaces two deep structural
hash caches with identity caches. V3 deduplicates one exact repeated
root-free-variable rewrite. The V2 and V3 changes are small wrappers around
the hash-pinned predecessor; the V1 proof-generation code is not forked.

`WPP_PROFILE_V2` is the authoritative static closure: 97 verified inputs,
comprising 20 Python modules and 77 fixed data/evidence files, with input-set
digest `E2CEA5925FB6A69A00544A01138356AC66C15B0CF614CF824D954BDB26725FF5`.
The historical top-level CLI contracts, profile builders/auditors, tests,
translation runners, session records, and final-result notes are archived
beside the implementation.

The historical C18 runtime additionally checked:

- the 9,945,323-byte accepted `.mm` source;
- a 14-resource alpha ancestry;
- 77 alpha `.olean` files and two profile `.olean` files; and
- the accepted C17 predecessor receipt and umbrella source.

Those 79 `.olean` files were inert certificates: the historical translator
read only their size/hash identity and never executed or deserialized them.
Palomar forbids compiled Lean outputs in a submitted tree, so their binary
payloads are not committed. Instead,
`archive/compiled_lean_evidence.json` retains every historical path, size, and
SHA-256 and joins each entry to an independently hash-pinned JSON authority by
JSON pointer. Its census is 77 alpha plus two profile certificates, totalling
21,417,512 historical bytes; its own SHA-256 is
`17532DD6BEBD20E3C45F110EE7CACAA1A69CFCB9784DB6E40CF0C30C40D224BD`.

Before exclusion from Git, all 79 payloads were independently rehashed against
the ledger. The public launcher validates the textual authority chain and
forbids attempts to open a virtual compiled artifact. The submitted Git tree
therefore has no `.olean`; a development checkout may retain ignored local
recovery copies, but they are unnecessary.

## Portable launcher

`portable_nominal_mm_translator_v1.py` is the first separately auditable
portability wrapper. It preserves all historical module/input hashes and
changes only two environment policies:

- it requires the CPython 3.12 language/runtime contract instead of one exact
  Windows `python.exe` hash; and
- it maps old absolute receipt paths at their canonical `work/` component into
  `translation/archive/work/`.

`portable_nominal_mm_translator_v2.py` is the public entry point. It retains
those relocation changes and installs a narrowly scoped virtual-path layer for
the 79 ledger entries. For those exact paths only, legacy existence/size/hash
queries are answered from the checked textual contracts; any attempt to read a
compiled payload raises an error. All ordinary source and receipt files still
have to exist and match their original hashes. During the frozen alpha-module
import, the same wrapper also interprets the basename of original Windows
receipt labels consistently on POSIX; it does not rewrite the archived module
or any hash-pinned record.

The v2 wrapper then installs the historical V2 identity-cache patch and V3 FV
deduplication patch. It requires only CPython 3.12's standard library. Its
SHA-256 is
`D481332291549E844ACA557158DDBB6A55EBBB5F7250EA1E87E5D7C1E47EA2F5`.
Because regenerated JSON receipts name the portable wrapper and current output
paths, their hashes are expected to differ. The emitted Lean sources and
semantic metrics must not.

The accepted C18 result has 67 theorems (ordinals 4,255–4,321), 1,227 proof
applications, application-trace hash
`B3354FF6DCEEF17BAE2C4A31F4CECD87FF7B1C56382E19346DD04B0CDAB4760A`,
seven compact FV normalizations, and zero generic DV fallbacks.

For the generic CLI in the committed, compiled-artifact-free package, pass the
historical arguments through v2:

```text
python translation/portable_nominal_mm_translator_v2.py --help
```

`reproduce_c18.py` is the recommended fixed, one-command C18 entry point. It
imports v2 and is also exercised by the repository's `research-archive` CI
job.

## Reuse and limits

The engine is reusable for another interval of this same supported
Metamath/Flypitch profile by selecting a source, endpoint, theorem interval,
accepted alpha frontier, and predecessor receipt. A project using new syntax
constructors or definition leaves needs a new frozen profile and corresponding
Lean support modules; the tool does not pretend that arbitrary Metamath
databases already satisfy the WPP profile.

On Windows, use a short checkout path (for example `C:\src\nf-wpp`) because
some preserved historical paths approach the legacy 260-character limit.
Linux is unaffected.

After source regeneration, the independent proof check remains the normal
Lean workflow: build `NFNotWPPProof`/`Solution`, audit the public theorem's
axioms, and run Comparator/NanoDa on Linux. The translator is not part of the
Lean trusted computing base. The textual compiled-evidence ledger documents
historical acceptance; it is not substituted for the current Lean kernel
build of the emitted sources.
