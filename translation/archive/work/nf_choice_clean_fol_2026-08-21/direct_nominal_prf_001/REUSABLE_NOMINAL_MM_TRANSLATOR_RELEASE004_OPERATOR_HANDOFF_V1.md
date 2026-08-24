# Reusable NF/WPP Metamath-to-Lean translator: Release004 operator handoff

Status date: 2026-08-23.  This is an append-only source/operator note.  It does
not authorize a Lean run and does not itself claim the final WPP endpoint.

## Bottom line

There is a reusable, fail-closed source translator now:
`reusable_nominal_mm_translator_v1.py`.  Given the exact supported flattened
NF/WPP Metamath source, an endpoint or closure interval, an accepted nominal
alpha frontier, and (for a continuation) an accepted predecessor resource, it:

1. parses and verifies every Metamath proof in the source;
2. reconstructs the selected endpoint dependency closure and proof DAG;
3. emits deterministic Lean theorem declarations using the existing nominal
   syntax/deduction constructors;
4. emits deterministic structural freshness/DV certificates;
5. partitions declarations only at theorem boundaries; and
6. publishes hash-pinned `.lean` parts, an umbrella `.lean`,
   `source_audit.json`, and `resource.json`.

It never invokes Lean.  Unsupported leaves, syntax/FV heads, alpha
definitions, source changes, predecessor mismatches, output reuse, or forbidden
generated tokens fail closed.  It does not use generic proof search and does
not emit `axiom`, `opaque`, `sorry`, or `admit` declarations.

For the present WPP endpoint, the convenience entry point
`run_nominal_wpp_remaining_replay_translation_v2.py` wraps that translator in
one source-only command.  Once supplied with an accepted Release004 alpha97
resource, it preflights and emits theorem ordinals 2867--4321: 1,455 Metamath
theorems in seven chained source chunks, ending at
`wppfiniteblocknotwppndv` (`(wn wwpp)`).

## What “translates in seconds” means

The seconds-scale claim applies to deterministic **source generation**, not to
Lean kernel verification.

- Release004 native alpha-source generation was measured at 13.812094 seconds
  for global 51, 23.967624 seconds for globals 52--71, and 39.533801 seconds
  for globals 72--97.  These timings are recorded in `a51ce4s1`, `a5271ce4s1`,
  and `a7297ce4s1` respectively.
- The 33.424749-second figure quoted earlier is the predecessor backend's
  W1--W26 alpha-source run.  It is representative, but it is not a timing of
  Lean and not a timing of the final 1,455-theorem replay command.
- Release004's additional fine/coarse source reshaping took 227.651062 and
  182.637154 seconds.  This is still source-only engineering work, but it is a
  minutes-scale packaging pass rather than proof checking.
- The final 1,455-theorem one-command replay has not yet been timed because it
  correctly refuses to run before an accepted alpha97 resource exists.  The
  runner invokes the checked translator once for a full preflight and once for
  each of seven chunks; do not advertise 33 seconds as a hard SLA for that
  eight-invocation job.
- Lean `--trust=0` compilation and `#print axioms` validation are a different
  phase.  For these very large generated terms that phase can take hours.  A
  slow kernel check is not slow Metamath translation.

## One command for the remaining WPP source

Run from `direct_nominal_prf_001`.  Replace the alpha resource path with the
actual accepted global-97 resource and use its exact hash.  All named output
paths must be absent.

```powershell
$python = 'C:\Users\glaze\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
$alpha97 = '.\r4c097k001\resource.json'
$alpha97Sha = (Get-FileHash -Algorithm SHA256 -LiteralPath $alpha97).Hash

& $python -B .\run_nominal_wpp_remaining_replay_translation_v2.py `
  --alpha-frontier-resource $alpha97 `
  --alpha-frontier-sha256 $alpha97Sha `
  --output-parent . `
  --session-resource .\nominal_wpp_remaining_replay_session_001.json `
  --adapter-output-dir .\nominal_alpha97_release004_replay_adapter_001
```

The command's fixed mathematical source input is:

- source:
  `../../mm0_conversion_2026-08-20/source_repair/hnwcut_resisomr_assist/endpoint_after_hnwcut_alias0_scope_repaired_mm0_importer_clean.mm`;
- source SHA-256:
  `868DF831E63E28AA924CC099510CD9E5D3BE18CD8416A20B335F5BBF3B42ED3F`;
- endpoint: `wppfiniteblocknotwppndv`;
- accepted predecessor: `k12ag002/resource.json`, SHA-256
  `EC9375ABE945791CECD7B4D5E48A07545B54042753D7C1A14258EC28AD041345`;
- interval: closure theorem ordinals 2867--4321;
- profile: `WPP_PROFILE_V2`; and
- split limit: 60,000 copied theorem bytes, with an oversized theorem retained
  intact as a singleton.

Successful output consists of:

- `nominal_alpha97_release004_replay_adapter_001/resource.json`;
- `nominal_wpp_remaining_replay_alpha97_preflight_001/resource.json`;
- seven directories
  `reusable_nominal_mm_translator_v1_chunk012b_compact_001` through
  `reusable_nominal_mm_translator_v1_chunk018_compact_001`, each containing
  hash-pinned `.lean` part files, an umbrella `.lean`, `source_audit.json`, and
  `resource.json`; and
- `nominal_wpp_remaining_replay_session_001.json`, which pins the complete
  source-only run and the final chunk resource.

None of those outputs is a kernel acceptance result.  Kernel-check the chunks
sequentially with `reusable_nominal_kernel_runner_release004_v2.ps1`, then run
the final endpoint package.  The exact post-alpha97 sequence is recorded in
`POST_ALPHA97_RELEASE004_REPLAY_COMMANDS_V1.md`.

## One command for a future supported endpoint or interval

Use the public CLI directly:

```powershell
& $python -B .\reusable_nominal_mm_translator_v1.py `
  --source <flattened-supported-source.mm> `
  --source-sha256 <SOURCE_SHA256> `
  --endpoint <METAMATH_LABEL> `
  --start-ordinal <FIRST> --end-ordinal <LAST> `
  --alpha-frontier-resource <accepted-alpha-resource.json> `
  --alpha-frontier-sha256 <ALPHA_RESOURCE_SHA256> `
  --predecessor-resource <accepted-or-source-predecessor-resource.json> `
  --predecessor-resource-sha256 <PREDECESSOR_RESOURCE_SHA256> `
  --output-dir <fresh-output-directory> `
  --split-bytes 60000 `
  --module-prefix <LeanModulePrefix> `
  --namespace NFChoice.DirectNominalPrf.WPPReplay `
  --wpp-profile WPP_PROFILE_V2
```

The ordinals are one-based theorem ordinals within the selected endpoint's
dependency closure, not raw database statement numbers.  For a prefix starting
at ordinal 1, omit both predecessor arguments.  To select the whole closure,
omit both ordinal arguments.  Add `--audit-only` for a source/coverage preflight
that emits no Lean modules; its output directory is still append-only and
cannot later be reused for emission.

## Exact supported scope

“Reusable” currently means the frozen NF/WPP target profile, not arbitrary
Metamath:

- the exact flattened repaired NF/WPP source and source/FV contract above;
- endpoints and intervals whose syntax constructors, FOL rules, eleven NF
  literal axioms, exceptional definition leaves, structural FV/DV heads, and
  nominal alpha-definition leaves are all covered by `WPP_PROFILE_V2`; and
- an accepted trust-zero alpha resource publishing exactly
  `[propext, Classical.choice, Quot.sound]` and a hash-valid predecessor chain.

The CLI rejects Metamath `$[ ... $]` includes.  A byte-changed source, a new
syntax/FV head, a new primitive axiom family, or a new definition universe
requires an append-only profile/registry update and audit.  An unrelated
Metamath database additionally needs Lean syntax constructors, FV equations,
primitive-leaf handlers, and a nominal alpha call-map.  The present tool is
therefore a reusable compiler for this NF/FOL formalism, not a universal
Metamath compiler.

## Frozen pins

| Role | Path | SHA-256 |
|---|---|---|
| Release004 manifest | `translator_release_nf_wpp_004/manifest.json` | `B8B1128D2AAFC5882BC7AB72B2EE0C821CE1CB76C96D6A4C9E8223AC56BEFE98` |
| Release004 independent audit | `translator_release_nf_wpp_004_audit_001/resource.json` | `75E81514492967A6B97552527977098455CAD4DA918AFC9F531AC6B82EAF5D7E` |
| Source translator | `reusable_nominal_mm_translator_v1.py` | `8ABE386FEC8BEE78499D25B3B488C4C81054019590789CC1AF71D4DC352F3A94` |
| Default profile | `WPP_PROFILE_V2.json` | `96B6A85D4B5B60023000C49BB40CF4F7DCD679AAF4DB6C796880A684DBF12949` |
| Release004 native backend | `compact_alpha_envfresh_backend_v3.py` | `263313DB66DC2FA43F113C0165D51ED8C890029A1413659F3BB52A7B001FFD07` |
| Release004 test record | `translator_release_nf_wpp_004/SOURCE_TEST_RESULTS_004.json` | `0616A4B6990276CE98897E4C7EFEAEDE008DC34D017F472B28D02FD6A075CC03` |
| Release004 alpha adapter | `adapt_release004_alpha_frontier_for_replay_v1.py` | `1EE1EA18512296B5604590B0C4E7EB7DB2622A32E1ED29407315B47D58BE6E70` |
| Remaining replay runner | `run_nominal_wpp_remaining_replay_translation_v2.py` | `7673A51FC97516C990951B9C80A4CCAC7A8EE4CAB0DE69DF1C3EE85829C83751` |
| Frozen remaining plan | `nominal_wpp_remaining_replay_staging_001/plan.json` | `F60772608E3074F98822234D8A541E2C952764EB8D5566B08B159EBB864AB628` |
| Release004 kernel wrapper | `reusable_nominal_kernel_runner_release004_v2.ps1` | `A7C56377F4358F8FEB0621042CA85814F7A5D85115F88EAB7786B9DD62A30681` |
| Compatibility audit | `release004_alpha_replay_compat_audit_001/resource.json` | `8C801FC4A05E2E4766D09B8D6145B0EBE360A2A19E0B10F1BFEEC32DF843BD15` |
| Independent compatibility audit | `release004_alpha_replay_compat_independent_audit_001/resource.json` | `3D19699C76E0E027CE2A4D14D48870E64E52C990A3BD1304FCE36CC02D14F696` |
| Post-alpha97 commands | `POST_ALPHA97_RELEASE004_REPLAY_COMMANDS_V1.md` | `65F8CB0F216177E48B8EB5AD91D17EB6570711E734FB4173AD687CC24D28CEEE` |
| Required Python executable | `C:/Users/glaze/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe` | `D8E3F0ADF246DB00358C0C4ED349CF714898178F9558FB0E944F79F5C07F8EAA` |

The Release004 V8 manifest remains valid source-provenance evidence, but its
coarse lifter misplaced a top-level `change` tactic at exactly globals 72 and
78.  The append-only V9 repair is the operational successor:

| V9 repair role | Path | SHA-256 |
|---|---|---|
| V9 lifter | `lift_compact_nominal_alpha_def_dag_v9.py` | `AC711A8F18687CF731412004316F8E0555A10B2A55ED2FBF7A0A303B89E3653D` |
| Two-repair authority | `r4c7278v9kbi2/resource.json` | `E8309A91DEA94AC8496899EF18A81F09319211F6D19BC265D3426269B2CCA707` |
| Authority audit | `r4c7278v9kbia2/resource.json` | `CEF12F8D4A9638B9FE657348856A71E313383999074021C6FD922010F5468C24` |
| Accepted global-72 kernel resource | `r4c072v9k001/resource.json` | `F7D7C7B2D836C273DADC42688EB82B8D3D5645E71BEEA340B76DBD2A597C8DBE` |
| Global-72 independent audit | `r4c072v9k001ia1/resource.json` | `648382BDD813F15B482A395D1F6987A1E90F234C560A045472CA84D337DE5400` |

## Source-only validation commands

Run these as separate Python processes from `direct_nominal_prf_001`.  The
separation matters because the compatibility suite intentionally rejects a
profile backend preloaded before its own hash verification.

```powershell
& $python -B -m unittest `
  test_reusable_nominal_mm_translator_v1.py `
  test_wpp_profile_v1.py `
  test_wpp_profile_v2.py `
  test_nominal_alpha_dispatch_core_v3.py `
  test_alpha_fresh_facts_simp_only_v1.py `
  test_compact_alpha_envfresh_backend_v2.py `
  test_compact_alpha_envfresh_backend_v3.py `
  test_compact_nominal_alpha_proof_data_pipeline_v1.py `
  test_native_notmem_mass_transform_contract_v1.py

& $python -B -m unittest -v test_release004_alpha_replay_compat_v1.py
& $python -B -m unittest -v test_nominal_wpp_remaining_replay_staging_v1.py
& $python -B -m unittest -v test_release004_public_change_lifter_v9.py
```

Observed on 2026-08-23, without invoking Lean: Release004 76/76 in 12.499
seconds; adapter 6/6 in 0.539 seconds; frozen plan 9/9 in 6.839 seconds; V9
repair 6/6 in 0.177 seconds.

Use `Get-FileHash -Algorithm SHA256 -LiteralPath <path>` to compare every
operator input with the table before use.  The existing independent audit is
append-only; `audit_translator_release_nf_wpp_004_v1.py` deliberately refuses
to overwrite it.

## Remaining ingredients and portability

There is one current in-profile prerequisite before the frozen remaining-WPP
one-command run can execute: an accepted trust-zero, exact-three Release004
resource ending at global alpha ordinal 97.  Global 72 is accepted; the
continuation to 97 is kernel work, not missing translator logic.

After alpha97 and the final replay are accepted, a later proof using an
already-covered endpoint in the same pinned source/profile can reuse the
translator and accepted alpha frontier immediately.  It does not need the
alpha constructors re-proved.

Two limits remain for broader reuse:

1. The frozen convenience runner pins the exact Python executable hash, and
   resource chains contain workspace-local paths.  Same-workspace reuse is
   ready; another machine needs the preserved directory layout and interpreter
   or a small append-only portability successor that re-authorizes them.
2. A changed or unrelated Metamath source needs a new audited target profile as
   described above.  That is profile-construction work, not a failure of the
   proof-DAG translator.
