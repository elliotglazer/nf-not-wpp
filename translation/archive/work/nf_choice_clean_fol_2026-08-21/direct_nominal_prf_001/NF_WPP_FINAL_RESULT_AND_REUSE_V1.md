# NF proves not-WPP: final result and reusable-tool handoff

Status date: 2026-08-24.

## Result

Lean 4 accepted the following public theorem under `--trust=0`:

```lean
theorem hailperinNF_proves_not_WPP :
    LiteralHailperinNF ⊢ₛ' Fol.bd_not SourceWPPFOL
```

The fully qualified declaration is
`NFChoice.DirectNominalPrf.Nominal.WPPFinalEndpointV1.hailperinNF_proves_not_WPP`.
Its generated source is
`nominal_wpp_final_endpoint_kernel_002/NominalWPPFinalEndpointV1.lean`.

The final kernel receipt is
`nominal_wpp_final_endpoint_kernel_002/resource.json`, SHA-256
`1B31418843E0968B566BCE7727F437AF05ACE311BC2B151AE84C4755CCBA9A08`.
Its exact status is
`PASS_TRUST_ZERO_EXACT_ELEVEN_NF_PROVES_NOT_WPP_EXACT_THREE`, and its
`failure` field is null.

Both final Lean invocations exited zero, were not killed, had empty stderr,
and used:

```text
--trust=0 --threads=1 -DmaxHeartbeats=5000000 -DmaxRecDepth=30000
```

The final `#print axioms` result is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

There is no project-local `axiom`, `opaque`, `sorry`, or `sorryAx` dependency.

## Exact object theory

`LiteralHailperinNF` is definitionally `Set.range literalAxiomFormula` over
the exact eleven-constructor type `HailperinAxiomName`:

1. `axExt`
2. `axNin`
3. `axXp`
4. `axCnv`
5. `ax1c`
6. `axSset`
7. `axSi`
8. `axIns2`
9. `axIns3`
10. `axTypeLower`
11. `axSn`

These eleven object-theory formulas are distinct from the three standard
Lean kernel dependencies reported by `#print axioms`.

The Metamath endpoint is theorem ordinal 4321,
`wppfiniteblocknotwppndv`, with parsed AST `(wn wwpp)`.  C18 exports it as:

```lean
NFChoice.DirectNominalPrf.WPPReplay.g_wppfiniteblocknotwppndv :
  Nominal.NPrf (.neg syn_wwpp)
```

The closed endpoint bridge turns that exact generated nominal proof into the
public syntactic Flypitch derivability judgment above.

## Provenance and independent audit

Key immutable records are:

| Role | Path | SHA-256 |
|---|---|---|
| Translator V3 | `reusable_nominal_mm_translator_v3.py` | `DECC5089EAB55B95806EB74742FD47A1EB127502B243811DD882737FCB98475F` |
| Translator V3 regression test | `test_reusable_nominal_mm_translator_v3.py` | `E630C1B2E5ACCE85573582768744F12C898552DD8C690388EF606152D4D82C5F` |
| Frozen source launcher V6 | `run_nominal_wpp_remaining_replay_translation_v6.py` | `0461A3CD01DA65854FA71636B74CCEAC0E23AB46F15A159617C34B15201F95DF` |
| Completed source session | `nominal_wpp_remaining_replay_session_002.json` | `522D4E24A195CB97892269ADBBF3C65CF6AF95B34218FF4CEABA2C85E19F8B55` |
| C18 source receipt | `reusable_nominal_mm_translator_v3_chunk018_compact_001/resource.json` | `44CCEF5B0AB6594EFDC867BF8E59A7B3A7EA37D5BD3235DECB3293AC52F80D75` |
| Generic kernel runner V3 | `reusable_nominal_kernel_runner_v3.ps1` | `E7E964D60B2BE30E6CCC41284C69FD92CF79A60C76A6DA64301599AAD103B238` |
| C18 kernel receipt | `k18g001/resource.json` | `B4FB07A8B17D67D480369A471E0CE33C4426BAC3369E2C3DCCA066355F3EB133` |
| Endpoint runner V2 | `run_nominal_wpp_final_endpoint_trust0_v2.ps1` | `6A523BFFFE87BCFF5C7C39116CC3F44A9DF70B6AF8B39C1207E9B44A4D8E1FDC` |
| Corrected endpoint template | `NOMINAL_WPP_FINAL_ENDPOINT_V2.lean.in` | `096B2BC67B9560CAD143C6DE84C202818DCA285DAFDAED75E2BF1AB69F34FECA` |
| Endpoint package audit 007 | `nominal_wpp_final_endpoint_package_source_audit_007/resource.json` | `4C7D29565A2B1F9032FBE8E1924A7ED35B93C85663E2CF6259F16EC5336E6EB4` |
| Final kernel receipt | `nominal_wpp_final_endpoint_kernel_002/resource.json` | `1B31418843E0968B566BCE7727F437AF05ACE311BC2B151AE84C4755CCBA9A08` |

Two read-only independent final audits passed.  One checked 84 endpoint
invariants.  The other rehashed 308 distinct linked files across the endpoint,
package-audit lineage, C18 source, WPP profile, K18 commands, support inputs,
and alpha oleans.  Both found zero mismatches.

The failed append-only directory `nominal_wpp_final_endpoint_kernel_001` is
preserved.  It records the harmless first-attempt template parse error in
which a qualified Lean name was split immediately after a dot.  Template V2
is an audited one-fragment successor; it changes no theorem, type, import, or
proof term.

## Measured size and compilation time

The public endpoint wrapper is 1,070 bytes of Lean source and compiles to an
8,200-byte `.olean`.  The closed bridge compiles to a 44,392-byte `.olean`.
The observed final pair took:

| Module | `--trust=0` time |
|---|---:|
| Closed endpoint bridge | 30.904 seconds |
| Public endpoint wrapper | 107.688 seconds |
| Total | 138.592 seconds |

Following the accepted kernel-receipt predecessor chain from C9 through C18
gives 488 unique replay source modules totaling 41,460,658 bytes (39.540 MiB).
Their compiled `.olean` files total 231,422,552 bytes (220.702 MiB).  The sum
of the recorded sequential `--trust=0` command times is 28,494.266 seconds,
or 7.915 hours.  This excludes rebuilding shared Flypitch, Mathlib, syntax,
and support dependencies.

Thus a cold independent replay check should budget about eight hours on this
machine once dependencies are installed.  Rechecking only the already-built
public endpoint takes about 2.3 minutes in the measured run; importing its
accepted `.olean` into a consumer is much faster.

## Reuse

For a future endpoint inside the same frozen repaired NF/WPP source and
`WPP_PROFILE_V2`, use `reusable_nominal_mm_translator_v3.py`.  Its public CLI
is unchanged from V1:

```powershell
python -B reusable_nominal_mm_translator_v3.py `
  --source <flattened-source.mm> `
  --source-sha256 <source-sha256> `
  --endpoint <Metamath-label> `
  --start-ordinal <first> --end-ordinal <last> `
  --alpha-frontier-resource <accepted-alpha-resource.json> `
  --alpha-frontier-sha256 <alpha-resource-sha256> `
  --predecessor-resource <accepted-predecessor-resource.json> `
  --predecessor-resource-sha256 <predecessor-resource-sha256> `
  --output-dir <fresh-output-directory> `
  --split-bytes 60000 `
  --module-prefix <LeanModulePrefix> `
  --namespace NFChoice.DirectNominalPrf.WPPReplay `
  --wpp-profile WPP_PROFILE_V2
```

The output directory must be fresh.  Omit both predecessor flags only for an
interval starting at closure ordinal 1.  Use `--audit-only` for a source-only
preflight.

Then run the generic `reusable_nominal_kernel_runner_v3.ps1` first with
`-PreflightOnly`, and again without it, supplying the emitted source receipt,
its SHA-256, the immediately preceding accepted kernel receipt and hash, and a
fresh output root.  It checks each generated module sequentially under
`--trust=0` and requires the exact ordered three-axiom print.

The translator performs deterministic source verification and generation; it
does not invoke Lean.  That phase remains seconds-to-minutes.  The hours-scale
part is independent elaboration and kernel checking of the large generated
terms.  The V3 regression suite currently passes 2/2 in 0.170 seconds.

This tool is immediately reusable for endpoints covered by the same NF/WPP
syntax, definition, freshness, and alpha profile.  A different Metamath
database or new object-language vocabulary still requires a new audited
profile supplying its syntax constructors, FV equations, primitive leaves,
and definition handlers.  The proof-DAG translation architecture and generic
kernel runner do not need to be redesigned.
