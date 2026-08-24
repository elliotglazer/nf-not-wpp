import NAR4C078C001Part085

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

theorem nb078_wpp_notmem_1335 (g : Var) : (nb078_alpha_dummy_548 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_548, fv_syn_c1c] using (nb078_compact_fv_empty_0403 g)

theorem nb078_compact_fv_empty_0404 : (nb078_alpha_dummy_544) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1336 : (nb078_alpha_dummy_544) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_544, fv_syn_c1c] using (nb078_compact_fv_empty_0404)

theorem nb078_compact_fv_empty_0405 (g : Var) : (nb078_alpha_dummy_547 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1337 (g : Var) : (nb078_alpha_dummy_547 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_547, fv_syn_c1c] using (nb078_compact_fv_empty_0405 g)

theorem nb078_compact_fv_empty_0406 : (nb078_alpha_dummy_543) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1338 : (nb078_alpha_dummy_543) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_543, fv_syn_c1c] using (nb078_compact_fv_empty_0406)

theorem nb078_compact_fv_empty_0407 (g : Var) : (nb078_alpha_dummy_546 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1339 (g : Var) : (nb078_alpha_dummy_546 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_546, fv_syn_c1c] using (nb078_compact_fv_empty_0407 g)

theorem nb078_compact_fv_empty_0408 : (nb078_alpha_dummy_541) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1340 : (nb078_alpha_dummy_541) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_541, fv_syn_c1c] using (nb078_compact_fv_empty_0408)

theorem nb078_compact_fv_empty_0409 (g : Var) : (nb078_alpha_dummy_542 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1341 (g : Var) : (nb078_alpha_dummy_542 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_542, fv_syn_c1c] using (nb078_compact_fv_empty_0409 g)

theorem nb078_compact_fv_empty_0410 : (nb078_alpha_dummy_537) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1342 : (nb078_alpha_dummy_537) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_537, fv_syn_c1c] using (nb078_compact_fv_empty_0410)

theorem nb078_compact_fv_empty_0411 (g : Var) : (nb078_alpha_dummy_539 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1343 (g : Var) : (nb078_alpha_dummy_539 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_539, fv_syn_c1c] using (nb078_compact_fv_empty_0411 g)

theorem nb078_compact_fv_empty_0412 : (nb078_alpha_dummy_538) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1344 : (nb078_alpha_dummy_538) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_538, fv_syn_c1c] using (nb078_compact_fv_empty_0412)

theorem nb078_compact_fv_empty_0413 (g : Var) : (nb078_alpha_dummy_540 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1345 (g : Var) : (nb078_alpha_dummy_540 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_540, fv_syn_c1c] using (nb078_compact_fv_empty_0413 g)

theorem nb078_compact_fv_empty_0414 : (nb078_alpha_dummy_530) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1346 : (nb078_alpha_dummy_530) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_530, fv_syn_c1c] using (nb078_compact_fv_empty_0414)

theorem nb078_compact_fv_empty_0415 (g : Var) : (nb078_alpha_dummy_532 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1347 (g : Var) : (nb078_alpha_dummy_532 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_532, fv_syn_c1c] using (nb078_compact_fv_empty_0415 g)

theorem nb078_compact_fv_empty_0416 : (nb078_alpha_dummy_529) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1348 : (nb078_alpha_dummy_529) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_529, fv_syn_c1c] using (nb078_compact_fv_empty_0416)

theorem nb078_compact_fv_empty_0417 (g : Var) : (nb078_alpha_dummy_531 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1349 (g : Var) : (nb078_alpha_dummy_531 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_531, fv_syn_c1c] using (nb078_compact_fv_empty_0417 g)

theorem nb078_compact_fv_empty_0418 : (nb078_alpha_dummy_535) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1350 : (nb078_alpha_dummy_535) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_535, fv_syn_c1c] using (nb078_compact_fv_empty_0418)

theorem nb078_compact_fv_empty_0419 (g : Var) : (nb078_alpha_dummy_536 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1351 (g : Var) : (nb078_alpha_dummy_536 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_536, fv_syn_c1c] using (nb078_compact_fv_empty_0419 g)

theorem nb078_compact_fv_empty_0420 : (nb078_alpha_dummy_533) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1352 : (nb078_alpha_dummy_533) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_533, fv_syn_c1c] using (nb078_compact_fv_empty_0420)

theorem nb078_compact_fv_empty_0421 (g : Var) : (nb078_alpha_dummy_534 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1353 (g : Var) : (nb078_alpha_dummy_534 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_534, fv_syn_c1c] using (nb078_compact_fv_empty_0421 g)

theorem nb078_wpp_notmem_1354 : (nb078_alpha_dummy_526) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_526, fv_syn_c1c] using (nb078_compact_fv_empty_0394)

theorem nb078_wpp_notmem_1355 (g : Var) : (nb078_alpha_dummy_528 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_528, fv_syn_c1c] using (nb078_compact_fv_empty_0395 g)

theorem nb078_wpp_notmem_1356 : (nb078_alpha_dummy_525) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_525, fv_syn_c1c] using (nb078_compact_fv_empty_0396)

theorem nb078_wpp_notmem_1357 (g : Var) : (nb078_alpha_dummy_527 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_527, fv_syn_c1c] using (nb078_compact_fv_empty_0397 g)

theorem nb078_wpp_notmem_1358 : (nb078_alpha_dummy_523) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_523, fv_syn_c1c] using (nb078_compact_fv_empty_0398)

theorem nb078_wpp_notmem_1359 (x : Var) (g : Var) : (nb078_alpha_dummy_524 x g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_524, fv_syn_c1c] using (nb078_compact_fv_empty_0399 x g)

theorem nb078_wpp_notmem_1360 : (nb078_alpha_dummy_521) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_521, fv_syn_c1c] using (nb078_compact_fv_empty_0400)

theorem nb078_wpp_notmem_1361 (x : Var) (g : Var) : (nb078_alpha_dummy_522 x g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_522, fv_syn_c1c] using (nb078_compact_fv_empty_0401 x g)

theorem nb078_compact_envfresh_0195 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_545), (nb078_alpha_dummy_548 g)), ((nb078_alpha_dummy_544), (nb078_alpha_dummy_547 g)), ((nb078_alpha_dummy_543), (nb078_alpha_dummy_546 g)), ((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)), ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)), ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_545) (nb078_alpha_dummy_548 g) (nb078_wpp_notmem_1334) (nb078_wpp_notmem_1335 g) (TEnvFresh.consFresh (nb078_alpha_dummy_544) (nb078_alpha_dummy_547 g) (nb078_wpp_notmem_1336) (nb078_wpp_notmem_1337 g) (TEnvFresh.consFresh (nb078_alpha_dummy_543) (nb078_alpha_dummy_546 g) (nb078_wpp_notmem_1338) (nb078_wpp_notmem_1339 g) (TEnvFresh.consFresh (nb078_alpha_dummy_541) (nb078_alpha_dummy_542 g) (nb078_wpp_notmem_1340) (nb078_wpp_notmem_1341 g) (TEnvFresh.consFresh (nb078_alpha_dummy_537) (nb078_alpha_dummy_539 g) (nb078_wpp_notmem_1342) (nb078_wpp_notmem_1343 g) (TEnvFresh.consFresh (nb078_alpha_dummy_538) (nb078_alpha_dummy_540 g) (nb078_wpp_notmem_1344) (nb078_wpp_notmem_1345 g) (TEnvFresh.consFresh (nb078_alpha_dummy_530) (nb078_alpha_dummy_532 g) (nb078_wpp_notmem_1346) (nb078_wpp_notmem_1347 g) (TEnvFresh.consFresh (nb078_alpha_dummy_529) (nb078_alpha_dummy_531 g) (nb078_wpp_notmem_1348) (nb078_wpp_notmem_1349 g) (TEnvFresh.consFresh (nb078_alpha_dummy_535) (nb078_alpha_dummy_536 g) (nb078_wpp_notmem_1350) (nb078_wpp_notmem_1351 g) (TEnvFresh.consFresh (nb078_alpha_dummy_533) (nb078_alpha_dummy_534 g) (nb078_wpp_notmem_1352) (nb078_wpp_notmem_1353 g) (TEnvFresh.consFresh (nb078_alpha_dummy_526) (nb078_alpha_dummy_528 g) (nb078_wpp_notmem_1354) (nb078_wpp_notmem_1355 g) (TEnvFresh.consFresh (nb078_alpha_dummy_525) (nb078_alpha_dummy_527 g) (nb078_wpp_notmem_1356) (nb078_wpp_notmem_1357 g) (TEnvFresh.consFresh (nb078_alpha_dummy_523) (nb078_alpha_dummy_524 x g) (nb078_wpp_notmem_1358) (nb078_wpp_notmem_1359 x g) (TEnvFresh.consFresh (nb078_alpha_dummy_521) (nb078_alpha_dummy_522 x g) (nb078_wpp_notmem_1360) (nb078_wpp_notmem_1361 x g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0756) (nb078_wpp_notmem_0757 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))

noncomputable def nb078_wpp_refl_0195 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_545), (nb078_alpha_dummy_548 g)), ((nb078_alpha_dummy_544), (nb078_alpha_dummy_547 g)), ((nb078_alpha_dummy_543), (nb078_alpha_dummy_546 g)), ((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)), ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)), ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0195 x y g)

theorem nb078_wpp_notmem_1362 : (nb078_alpha_dummy_545) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_545, fv_syn_c0] using (nb078_compact_fv_empty_0402)

theorem nb078_wpp_notmem_1363 (g : Var) : (nb078_alpha_dummy_548 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_548, fv_syn_c0] using (nb078_compact_fv_empty_0403 g)

theorem nb078_wpp_notmem_1364 : (nb078_alpha_dummy_544) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_544, fv_syn_c0] using (nb078_compact_fv_empty_0404)

theorem nb078_wpp_notmem_1365 (g : Var) : (nb078_alpha_dummy_547 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_547, fv_syn_c0] using (nb078_compact_fv_empty_0405 g)

theorem nb078_wpp_notmem_1366 : (nb078_alpha_dummy_543) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_543, fv_syn_c0] using (nb078_compact_fv_empty_0406)

theorem nb078_wpp_notmem_1367 (g : Var) : (nb078_alpha_dummy_546 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_546, fv_syn_c0] using (nb078_compact_fv_empty_0407 g)

theorem nb078_wpp_notmem_1368 : (nb078_alpha_dummy_541) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_541, fv_syn_c0] using (nb078_compact_fv_empty_0408)

theorem nb078_wpp_notmem_1369 (g : Var) : (nb078_alpha_dummy_542 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_542, fv_syn_c0] using (nb078_compact_fv_empty_0409 g)

theorem nb078_wpp_notmem_1370 : (nb078_alpha_dummy_537) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_537, fv_syn_c0] using (nb078_compact_fv_empty_0410)

theorem nb078_wpp_notmem_1371 (g : Var) : (nb078_alpha_dummy_539 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_539, fv_syn_c0] using (nb078_compact_fv_empty_0411 g)

theorem nb078_wpp_notmem_1372 : (nb078_alpha_dummy_538) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_538, fv_syn_c0] using (nb078_compact_fv_empty_0412)

theorem nb078_wpp_notmem_1373 (g : Var) : (nb078_alpha_dummy_540 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_540, fv_syn_c0] using (nb078_compact_fv_empty_0413 g)

theorem nb078_wpp_notmem_1374 : (nb078_alpha_dummy_530) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_530, fv_syn_c0] using (nb078_compact_fv_empty_0414)

theorem nb078_wpp_notmem_1375 (g : Var) : (nb078_alpha_dummy_532 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_532, fv_syn_c0] using (nb078_compact_fv_empty_0415 g)

theorem nb078_wpp_notmem_1376 : (nb078_alpha_dummy_529) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_529, fv_syn_c0] using (nb078_compact_fv_empty_0416)

theorem nb078_wpp_notmem_1377 (g : Var) : (nb078_alpha_dummy_531 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_531, fv_syn_c0] using (nb078_compact_fv_empty_0417 g)

theorem nb078_wpp_notmem_1378 : (nb078_alpha_dummy_535) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_535, fv_syn_c0] using (nb078_compact_fv_empty_0418)

theorem nb078_wpp_notmem_1379 (g : Var) : (nb078_alpha_dummy_536 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_536, fv_syn_c0] using (nb078_compact_fv_empty_0419 g)

theorem nb078_wpp_notmem_1380 : (nb078_alpha_dummy_533) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_533, fv_syn_c0] using (nb078_compact_fv_empty_0420)

theorem nb078_wpp_notmem_1381 (g : Var) : (nb078_alpha_dummy_534 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_534, fv_syn_c0] using (nb078_compact_fv_empty_0421 g)

theorem nb078_wpp_notmem_1382 : (nb078_alpha_dummy_526) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_526, fv_syn_c0] using (nb078_compact_fv_empty_0394)

theorem nb078_wpp_notmem_1383 (g : Var) : (nb078_alpha_dummy_528 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_528, fv_syn_c0] using (nb078_compact_fv_empty_0395 g)

theorem nb078_wpp_notmem_1384 : (nb078_alpha_dummy_525) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_525, fv_syn_c0] using (nb078_compact_fv_empty_0396)

theorem nb078_wpp_notmem_1385 (g : Var) : (nb078_alpha_dummy_527 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_527, fv_syn_c0] using (nb078_compact_fv_empty_0397 g)

theorem nb078_wpp_notmem_1386 : (nb078_alpha_dummy_523) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_523, fv_syn_c0] using (nb078_compact_fv_empty_0398)

theorem nb078_wpp_notmem_1387 (x : Var) (g : Var) : (nb078_alpha_dummy_524 x g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_524, fv_syn_c0] using (nb078_compact_fv_empty_0399 x g)

theorem nb078_wpp_notmem_1388 : (nb078_alpha_dummy_521) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_521, fv_syn_c0] using (nb078_compact_fv_empty_0400)

theorem nb078_wpp_notmem_1389 (x : Var) (g : Var) : (nb078_alpha_dummy_522 x g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_522, fv_syn_c0] using (nb078_compact_fv_empty_0401 x g)

theorem nb078_compact_envfresh_0196 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_545), (nb078_alpha_dummy_548 g)), ((nb078_alpha_dummy_544), (nb078_alpha_dummy_547 g)), ((nb078_alpha_dummy_543), (nb078_alpha_dummy_546 g)), ((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)), ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)), ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_545) (nb078_alpha_dummy_548 g) (nb078_wpp_notmem_1362) (nb078_wpp_notmem_1363 g) (TEnvFresh.consFresh (nb078_alpha_dummy_544) (nb078_alpha_dummy_547 g) (nb078_wpp_notmem_1364) (nb078_wpp_notmem_1365 g) (TEnvFresh.consFresh (nb078_alpha_dummy_543) (nb078_alpha_dummy_546 g) (nb078_wpp_notmem_1366) (nb078_wpp_notmem_1367 g) (TEnvFresh.consFresh (nb078_alpha_dummy_541) (nb078_alpha_dummy_542 g) (nb078_wpp_notmem_1368) (nb078_wpp_notmem_1369 g) (TEnvFresh.consFresh (nb078_alpha_dummy_537) (nb078_alpha_dummy_539 g) (nb078_wpp_notmem_1370) (nb078_wpp_notmem_1371 g) (TEnvFresh.consFresh (nb078_alpha_dummy_538) (nb078_alpha_dummy_540 g) (nb078_wpp_notmem_1372) (nb078_wpp_notmem_1373 g) (TEnvFresh.consFresh (nb078_alpha_dummy_530) (nb078_alpha_dummy_532 g) (nb078_wpp_notmem_1374) (nb078_wpp_notmem_1375 g) (TEnvFresh.consFresh (nb078_alpha_dummy_529) (nb078_alpha_dummy_531 g) (nb078_wpp_notmem_1376) (nb078_wpp_notmem_1377 g) (TEnvFresh.consFresh (nb078_alpha_dummy_535) (nb078_alpha_dummy_536 g) (nb078_wpp_notmem_1378) (nb078_wpp_notmem_1379 g) (TEnvFresh.consFresh (nb078_alpha_dummy_533) (nb078_alpha_dummy_534 g) (nb078_wpp_notmem_1380) (nb078_wpp_notmem_1381 g) (TEnvFresh.consFresh (nb078_alpha_dummy_526) (nb078_alpha_dummy_528 g) (nb078_wpp_notmem_1382) (nb078_wpp_notmem_1383 g) (TEnvFresh.consFresh (nb078_alpha_dummy_525) (nb078_alpha_dummy_527 g) (nb078_wpp_notmem_1384) (nb078_wpp_notmem_1385 g) (TEnvFresh.consFresh (nb078_alpha_dummy_523) (nb078_alpha_dummy_524 x g) (nb078_wpp_notmem_1386) (nb078_wpp_notmem_1387 x g) (TEnvFresh.consFresh (nb078_alpha_dummy_521) (nb078_alpha_dummy_522 x g) (nb078_wpp_notmem_1388) (nb078_wpp_notmem_1389 x g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0788) (nb078_wpp_notmem_0789 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))

noncomputable def nb078_wpp_refl_0196 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_545), (nb078_alpha_dummy_548 g)), ((nb078_alpha_dummy_544), (nb078_alpha_dummy_547 g)), ((nb078_alpha_dummy_543), (nb078_alpha_dummy_546 g)), ((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)), ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)), ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0196 x y g)

theorem nb078_wpp_notmem_1390 : (nb078_alpha_dummy_541) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_541, fv_syn_cnnc] using (nb078_compact_fv_empty_0408)

theorem nb078_wpp_notmem_1391 (g : Var) : (nb078_alpha_dummy_542 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_542, fv_syn_cnnc] using (nb078_compact_fv_empty_0409 g)

theorem nb078_wpp_notmem_1392 : (nb078_alpha_dummy_537) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_537, fv_syn_cnnc] using (nb078_compact_fv_empty_0410)

theorem nb078_wpp_notmem_1393 (g : Var) : (nb078_alpha_dummy_539 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_539, fv_syn_cnnc] using (nb078_compact_fv_empty_0411 g)

theorem nb078_wpp_notmem_1394 : (nb078_alpha_dummy_538) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_538, fv_syn_cnnc] using (nb078_compact_fv_empty_0412)

theorem nb078_wpp_notmem_1395 (g : Var) : (nb078_alpha_dummy_540 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_540, fv_syn_cnnc] using (nb078_compact_fv_empty_0413 g)

theorem nb078_wpp_notmem_1396 : (nb078_alpha_dummy_530) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_530, fv_syn_cnnc] using (nb078_compact_fv_empty_0414)

theorem nb078_wpp_notmem_1397 (g : Var) : (nb078_alpha_dummy_532 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_532, fv_syn_cnnc] using (nb078_compact_fv_empty_0415 g)

theorem nb078_wpp_notmem_1398 : (nb078_alpha_dummy_529) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_529, fv_syn_cnnc] using (nb078_compact_fv_empty_0416)

theorem nb078_wpp_notmem_1399 (g : Var) : (nb078_alpha_dummy_531 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_531, fv_syn_cnnc] using (nb078_compact_fv_empty_0417 g)

theorem nb078_wpp_notmem_1400 : (nb078_alpha_dummy_535) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_535, fv_syn_cnnc] using (nb078_compact_fv_empty_0418)

theorem nb078_wpp_notmem_1401 (g : Var) : (nb078_alpha_dummy_536 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_536, fv_syn_cnnc] using (nb078_compact_fv_empty_0419 g)

theorem nb078_wpp_notmem_1402 : (nb078_alpha_dummy_533) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_533, fv_syn_cnnc] using (nb078_compact_fv_empty_0420)

theorem nb078_wpp_notmem_1403 (g : Var) : (nb078_alpha_dummy_534 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_534, fv_syn_cnnc] using (nb078_compact_fv_empty_0421 g)

theorem nb078_wpp_notmem_1404 : (nb078_alpha_dummy_526) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_526, fv_syn_cnnc] using (nb078_compact_fv_empty_0394)

theorem nb078_wpp_notmem_1405 (g : Var) : (nb078_alpha_dummy_528 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_528, fv_syn_cnnc] using (nb078_compact_fv_empty_0395 g)

theorem nb078_wpp_notmem_1406 : (nb078_alpha_dummy_525) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_525, fv_syn_cnnc] using (nb078_compact_fv_empty_0396)

theorem nb078_wpp_notmem_1407 (g : Var) : (nb078_alpha_dummy_527 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_527, fv_syn_cnnc] using (nb078_compact_fv_empty_0397 g)

theorem nb078_wpp_notmem_1408 : (nb078_alpha_dummy_523) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_523, fv_syn_cnnc] using (nb078_compact_fv_empty_0398)

theorem nb078_wpp_notmem_1409 (x : Var) (g : Var) : (nb078_alpha_dummy_524 x g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_524, fv_syn_cnnc] using (nb078_compact_fv_empty_0399 x g)

theorem nb078_wpp_notmem_1410 : (nb078_alpha_dummy_521) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_521, fv_syn_cnnc] using (nb078_compact_fv_empty_0400)

theorem nb078_wpp_notmem_1411 (x : Var) (g : Var) : (nb078_alpha_dummy_522 x g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_522, fv_syn_cnnc] using (nb078_compact_fv_empty_0401 x g)

theorem nb078_compact_envfresh_0197 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)), ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)), ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_541) (nb078_alpha_dummy_542 g) (nb078_wpp_notmem_1390) (nb078_wpp_notmem_1391 g) (TEnvFresh.consFresh (nb078_alpha_dummy_537) (nb078_alpha_dummy_539 g) (nb078_wpp_notmem_1392) (nb078_wpp_notmem_1393 g) (TEnvFresh.consFresh (nb078_alpha_dummy_538) (nb078_alpha_dummy_540 g) (nb078_wpp_notmem_1394) (nb078_wpp_notmem_1395 g) (TEnvFresh.consFresh (nb078_alpha_dummy_530) (nb078_alpha_dummy_532 g) (nb078_wpp_notmem_1396) (nb078_wpp_notmem_1397 g) (TEnvFresh.consFresh (nb078_alpha_dummy_529) (nb078_alpha_dummy_531 g) (nb078_wpp_notmem_1398) (nb078_wpp_notmem_1399 g) (TEnvFresh.consFresh (nb078_alpha_dummy_535) (nb078_alpha_dummy_536 g) (nb078_wpp_notmem_1400) (nb078_wpp_notmem_1401 g) (TEnvFresh.consFresh (nb078_alpha_dummy_533) (nb078_alpha_dummy_534 g) (nb078_wpp_notmem_1402) (nb078_wpp_notmem_1403 g) (TEnvFresh.consFresh (nb078_alpha_dummy_526) (nb078_alpha_dummy_528 g) (nb078_wpp_notmem_1404) (nb078_wpp_notmem_1405 g) (TEnvFresh.consFresh (nb078_alpha_dummy_525) (nb078_alpha_dummy_527 g) (nb078_wpp_notmem_1406) (nb078_wpp_notmem_1407 g) (TEnvFresh.consFresh (nb078_alpha_dummy_523) (nb078_alpha_dummy_524 x g) (nb078_wpp_notmem_1408) (nb078_wpp_notmem_1409 x g) (TEnvFresh.consFresh (nb078_alpha_dummy_521) (nb078_alpha_dummy_522 x g) (nb078_wpp_notmem_1410) (nb078_wpp_notmem_1411 x g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0814) (nb078_wpp_notmem_0815 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))

noncomputable def nb078_wpp_refl_0197 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)), ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)), ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0197 x y g)

noncomputable def nb078_split_alpha_0058 (x : Var) (y : Var) (g : Var) : TAlphaWff [((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)), ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_535)) (Class.cab (nb078_alpha_dummy_529) (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526)) (Wff.classEq (Class.cv (nb078_alpha_dummy_529)) (syn_cphi (Class.cv (nb078_alpha_dummy_530))))))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_535)) (Class.cab (nb078_alpha_dummy_529) (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526)) (Wff.classEq (Class.cv (nb078_alpha_dummy_529)) (syn_cphi (Class.cv (nb078_alpha_dummy_530))))))))) (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_536 g)) (Class.cab (nb078_alpha_dummy_531 g) (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))))))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_536 g)) (Class.cab (nb078_alpha_dummy_531 g) (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0540) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0542 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0540) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0542 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0544) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0545 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0541) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0543 g) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_526))).fv ∪ ((Class.cv (nb078_alpha_dummy_525))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_527 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0546) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0547 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0546) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0547 g) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_530))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_532 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0550) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0551 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0550) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0551 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0548) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0549 g) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_545), (nb078_alpha_dummy_548 g)), ((nb078_alpha_dummy_544), (nb078_alpha_dummy_547 g)), ((nb078_alpha_dummy_543), (nb078_alpha_dummy_546 g)), ((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)), ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)), ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0195 x y g))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0554) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0555 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0552) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0553 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0558) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0559 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0556) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0557 g) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0554) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0555 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0552) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0553 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0558) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0559 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0556) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0557 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_545), (nb078_alpha_dummy_548 g)), ((nb078_alpha_dummy_544), (nb078_alpha_dummy_547 g)), ((nb078_alpha_dummy_543), (nb078_alpha_dummy_546 g)), ((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)), ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)), ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0196 x y g))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0562) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0563 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0560) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0561 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0562) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0563 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0560) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0561 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0566) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0567 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0564) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0565 g) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0566) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0567 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0564) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0565 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0548) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0549 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)), ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)), ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0197 x y g))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0548) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0549 g) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0548) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0549 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)), ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)), ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0197 x y g)))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0540) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0542 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0540) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0542 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0544) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0545 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0541) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0543 g) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_526))).fv ∪ ((Class.cv (nb078_alpha_dummy_525))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_527 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0546) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0547 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0546) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0547 g) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_530))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_532 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0550) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0551 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0550) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0551 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0548) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0549 g) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_545), (nb078_alpha_dummy_548 g)), ((nb078_alpha_dummy_544), (nb078_alpha_dummy_547 g)), ((nb078_alpha_dummy_543), (nb078_alpha_dummy_546 g)), ((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)), ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)), ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0195 x y g))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0554) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0555 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0552) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0553 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0558) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0559 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0556) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0557 g) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0554) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0555 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0552) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0553 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0558) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0559 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0556) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0557 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_545), (nb078_alpha_dummy_548 g)), ((nb078_alpha_dummy_544), (nb078_alpha_dummy_547 g)), ((nb078_alpha_dummy_543), (nb078_alpha_dummy_546 g)), ((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)), ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)), ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0196 x y g))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0562) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0563 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0560) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0561 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0562) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0563 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0560) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0561 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0566) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0567 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0564) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0565 g) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0566) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0567 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0564) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0565 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0548) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0549 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)), ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)), ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0197 x y g))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0548) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0549 g) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0548) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0549 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)), ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)), ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0197 x y g))))))))))))))))))))))))))))

theorem nb078_compact_fv_empty_0422 : (nb078_alpha_dummy_563) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1412 : (nb078_alpha_dummy_563) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_563, fv_syn_c1c] using (nb078_compact_fv_empty_0422)

theorem nb078_compact_fv_empty_0423 (g : Var) : (nb078_alpha_dummy_564 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1413 (g : Var) : (nb078_alpha_dummy_564 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_564, fv_syn_c1c] using (nb078_compact_fv_empty_0423 g)

theorem nb078_compact_fv_empty_0424 : (nb078_alpha_dummy_561) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1414 : (nb078_alpha_dummy_561) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_561, fv_syn_c1c] using (nb078_compact_fv_empty_0424)

theorem nb078_compact_fv_empty_0425 (g : Var) : (nb078_alpha_dummy_562 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1415 (g : Var) : (nb078_alpha_dummy_562 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_562, fv_syn_c1c] using (nb078_compact_fv_empty_0425 g)

theorem nb078_compact_fv_empty_0426 : (nb078_alpha_dummy_559) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1416 : (nb078_alpha_dummy_559) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_559, fv_syn_c1c] using (nb078_compact_fv_empty_0426)

theorem nb078_compact_fv_empty_0427 (g : Var) : (nb078_alpha_dummy_560 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1417 (g : Var) : (nb078_alpha_dummy_560 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_560, fv_syn_c1c] using (nb078_compact_fv_empty_0427 g)

theorem nb078_compact_envfresh_0198 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_545), (nb078_alpha_dummy_548 g)), ((nb078_alpha_dummy_544), (nb078_alpha_dummy_547 g)), ((nb078_alpha_dummy_543), (nb078_alpha_dummy_546 g)), ((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)), ((nb078_alpha_dummy_563), (nb078_alpha_dummy_564 g)), ((nb078_alpha_dummy_561), (nb078_alpha_dummy_562 g)), ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_559), (nb078_alpha_dummy_560 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)), ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_545) (nb078_alpha_dummy_548 g) (nb078_wpp_notmem_1334) (nb078_wpp_notmem_1335 g) (TEnvFresh.consFresh (nb078_alpha_dummy_544) (nb078_alpha_dummy_547 g) (nb078_wpp_notmem_1336) (nb078_wpp_notmem_1337 g) (TEnvFresh.consFresh (nb078_alpha_dummy_543) (nb078_alpha_dummy_546 g) (nb078_wpp_notmem_1338) (nb078_wpp_notmem_1339 g) (TEnvFresh.consFresh (nb078_alpha_dummy_541) (nb078_alpha_dummy_542 g) (nb078_wpp_notmem_1340) (nb078_wpp_notmem_1341 g) (TEnvFresh.consFresh (nb078_alpha_dummy_537) (nb078_alpha_dummy_539 g) (nb078_wpp_notmem_1342) (nb078_wpp_notmem_1343 g) (TEnvFresh.consFresh (nb078_alpha_dummy_538) (nb078_alpha_dummy_540 g) (nb078_wpp_notmem_1344) (nb078_wpp_notmem_1345 g) (TEnvFresh.consFresh (nb078_alpha_dummy_563) (nb078_alpha_dummy_564 g) (nb078_wpp_notmem_1412) (nb078_wpp_notmem_1413 g) (TEnvFresh.consFresh (nb078_alpha_dummy_561) (nb078_alpha_dummy_562 g) (nb078_wpp_notmem_1414) (nb078_wpp_notmem_1415 g) (TEnvFresh.consFresh (nb078_alpha_dummy_530) (nb078_alpha_dummy_532 g) (nb078_wpp_notmem_1346) (nb078_wpp_notmem_1347 g) (TEnvFresh.consFresh (nb078_alpha_dummy_529) (nb078_alpha_dummy_531 g) (nb078_wpp_notmem_1348) (nb078_wpp_notmem_1349 g) (TEnvFresh.consFresh (nb078_alpha_dummy_559) (nb078_alpha_dummy_560 g) (nb078_wpp_notmem_1416) (nb078_wpp_notmem_1417 g) (TEnvFresh.consFresh (nb078_alpha_dummy_533) (nb078_alpha_dummy_534 g) (nb078_wpp_notmem_1352) (nb078_wpp_notmem_1353 g) (TEnvFresh.consFresh (nb078_alpha_dummy_526) (nb078_alpha_dummy_528 g) (nb078_wpp_notmem_1354) (nb078_wpp_notmem_1355 g) (TEnvFresh.consFresh (nb078_alpha_dummy_525) (nb078_alpha_dummy_527 g) (nb078_wpp_notmem_1356) (nb078_wpp_notmem_1357 g) (TEnvFresh.consFresh (nb078_alpha_dummy_523) (nb078_alpha_dummy_524 x g) (nb078_wpp_notmem_1358) (nb078_wpp_notmem_1359 x g) (TEnvFresh.consFresh (nb078_alpha_dummy_521) (nb078_alpha_dummy_522 x g) (nb078_wpp_notmem_1360) (nb078_wpp_notmem_1361 x g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0756) (nb078_wpp_notmem_0757 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))

noncomputable def nb078_wpp_refl_0198 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_545), (nb078_alpha_dummy_548 g)), ((nb078_alpha_dummy_544), (nb078_alpha_dummy_547 g)), ((nb078_alpha_dummy_543), (nb078_alpha_dummy_546 g)), ((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)), ((nb078_alpha_dummy_563), (nb078_alpha_dummy_564 g)), ((nb078_alpha_dummy_561), (nb078_alpha_dummy_562 g)), ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_559), (nb078_alpha_dummy_560 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)), ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0198 x y g)

theorem nb078_wpp_notmem_1418 : (nb078_alpha_dummy_563) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_563, fv_syn_c0] using (nb078_compact_fv_empty_0422)

theorem nb078_wpp_notmem_1419 (g : Var) : (nb078_alpha_dummy_564 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_564, fv_syn_c0] using (nb078_compact_fv_empty_0423 g)

theorem nb078_wpp_notmem_1420 : (nb078_alpha_dummy_561) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_561, fv_syn_c0] using (nb078_compact_fv_empty_0424)

theorem nb078_wpp_notmem_1421 (g : Var) : (nb078_alpha_dummy_562 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_562, fv_syn_c0] using (nb078_compact_fv_empty_0425 g)

theorem nb078_wpp_notmem_1422 : (nb078_alpha_dummy_559) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_559, fv_syn_c0] using (nb078_compact_fv_empty_0426)

theorem nb078_wpp_notmem_1423 (g : Var) : (nb078_alpha_dummy_560 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_560, fv_syn_c0] using (nb078_compact_fv_empty_0427 g)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
